module Control.Grammar.Combinators

import Control.Grammar
import Control.Monad.Identity
import Generics.Derive

%language ElabReflection

export
optional : GrammarT e t m a -> GrammarT e t m (Maybe a)
optional g = Just <$> g <|> pure Nothing

mutual
  export
  some : GrammarT e t m a -> GrammarT e t m (n ** Vect (S n) a)
  some g = do
    x <- optional g
    case x of
         Nothing => Fail ErrorNoConsumption
         Just y => do
           (n ** ys) <- many g
           pure $ (n ** y :: ys)

  export
  many : GrammarT e t m a -> GrammarT e t m (n ** Vect n a)
  many g = gSome <|> pure (0 ** Data.Vect.Nil)
    where
      gSome : GrammarT e t m (n ** Vect n a)
      gSome = do
        (nSome ** vSome) <- some g
        pure (S nSome ** vSome)

mutual
  export
  someTill : (gEnd : GrammarT e t m b) ->
             (g : GrammarT e t m a) ->
             GrammarT e t m (n ** Vect (S n) a)
  someTill gEnd g = do
    x <- g
    (n ** xs) <- manyTill gEnd g
    pure $ (n ** x :: xs)

  export
  manyTill : (gEnd : GrammarT e t m b) ->
             (g : GrammarT e t m a) ->
             GrammarT e t m (n ** Vect n a)
  manyTill gEnd g = do
    x <- optional gEnd
    case x of
         Nothing => do
           (nSome ** vSome) <- someTill gEnd g
           pure (S nSome ** vSome)
         Just y => pure (0 ** Data.Vect.Nil)
