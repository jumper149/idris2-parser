module Control.Grammar

import Control.Monad.Identity
import Control.Monad.Error.Interface
import Generics.Derive

%language ElabReflection

public export
data ParseError : e -> Type where
  ErrorEmpty : ParseError e
  ErrorNotEmpty : ParseError e
  ErrorNoConsumption : ParseError e
  Error : e -> ParseError e

-- e: Error
-- t: Token
-- m: Monad
-- a: return value
public export
data GrammarT : e -> t -> m -> (a : Type) -> Type where
  Return : (value : a) ->
           GrammarT e t m a
  Fail : (error : ParseError e) ->
         GrammarT e t m a
  End : GrammarT e t m ()
  Terminal : (consume : t -> Either e a) ->
             GrammarT e t m a
  Sequence : (gx : GrammarT e t m a) ->
             (gf : a -> GrammarT e t m b) ->
             GrammarT e t m b
  Alternate : (g1 : GrammarT e t m a) ->
              (g2 : Lazy (GrammarT e t m a)) ->
              GrammarT e t m a

export
Functor (GrammarT e t m) where
  map f g = case g of
    Return value => Return $ f value
    Fail error => Fail error
    End => Sequence End (Return . f)
    Terminal consume => Terminal $ map f . consume
    Sequence gx gf => Sequence gx $ map f . gf
    Alternate g1 g2 => Alternate (map f g1) (map f g2)

export
Applicative (GrammarT e t m) where
  pure = Return
  (<*>) gf gx = Sequence gf $ \ f => map f gx

export
Alternative (GrammarT e t m) where
  empty = Fail ErrorEmpty
  (<|>) = Alternate

export
Monad (GrammarT e t m) where
  (>>=) = Sequence

export
Monad m => MonadError e (GrammarT e t m) where
  throwError = Fail . Error
  catchError (Fail (Error error)) catch = catch error
  catchError fail@(Fail _) _ = fail
  catchError succeed _ = succeed

export
end : GrammarT e t m ()
end = End

export
terminal : (consume : t -> Either e a) -> GrammarT e t m a
terminal = Terminal

public export
Grammar : (e : Type) -> (t : Type) -> (a : Type) -> Type
Grammar e t a = GrammarT e t Identity a

export
runParser : List t -> Grammar e t a -> (Either (ParseError e) a, List t)
runParser l p = case p of
  Return value => (Right value, l)
  Fail error => (Left error, l)
  End => case l of
    [] => (Right (), l)
    x :: xs => (Left ErrorNotEmpty, l)
  Terminal consume => case l of
    [] => (Left ErrorEmpty, l)
    x :: xs => case consume x of
      Left error => (Left $ Error error, xs)
      Right value => (Right value, xs)
  Sequence gx gf => case runParser l gx of
    (Left gxError, gxL) => (Left gxError, gxL)
    (Right gxValue, gxL) => runParser gxL $ gf gxValue
  Alternate g1 g2 => case runParser l g1 of
    (Right g1Value, g1L) => (Right g1Value, g1L)
    (Left g1Error, g1L) => runParser l g2
