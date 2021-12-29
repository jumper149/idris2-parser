module Main

import Control.Monad.Error.Interface
import Control.Monad.Identity
import Control.Grammar
import Control.Grammar.Combinators
import Data.Fin
import Data.Vect

export
char : Char -> e -> Grammar e Char ()
char chr error = terminal $ \ x =>
  if x == chr
     then pure ()
     else throwError error

export
string : String -> e -> Grammar e Char ()
string str error = traverse_ (\ x => char x error) $ unpack str

export
newline : e -> Grammar e Char ()
newline error = terminal $ \case
  '\n' => Right ()
  _ => Left error

export
space : e -> Grammar e Char ()
space error = terminal $ \case
  ' ' => Right ()
  _ => Left error

export
spaces : e -> Grammar e Char ()
spaces error = some (space error) *> pure ()

export
digit : e -> Grammar e Char (Fin 10)
digit error = terminal $ \case
  '0' => Right 0
  '1' => Right 1
  '2' => Right 2
  '3' => Right 3
  '4' => Right 4
  '5' => Right 5
  '6' => Right 6
  '7' => Right 7
  '8' => Right 8
  '9' => Right 9
  _ => Left error

export
nat : e -> Grammar e Char Nat
nat error = do
  (_ ** digits) <- some $ digit error
  pure $ foldl (\ acc, next => 10 * acc + next) 0 $ finToNat <$> digits
