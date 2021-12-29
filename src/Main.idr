module Main

import Control.Monad.Identity
import Control.Grammar
import Control.Grammar.Char
import Control.Grammar.Combinators
import Data.Fin
import Data.Vect

-- Parse:
-- "10 -> 20"
data Token = TokenNat Nat
           | TokenWhitespace
           | TokenArrow

g : Grammar String Char Token
g = choice ( (TokenNat <$> nat "errNat")
          :: (space "errSpace" *> pure TokenWhitespace)
          :: (string "->" "errSpace" *> pure TokenArrow)
          :: Data.Vect.Nil)

main : IO ()
main = putStrLn "Hello world!"
