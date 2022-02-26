module Control.Grammar.Core

import Control.Monad.Identity
import Control.Monad.Error.Interface
import Generics.Derive

%language ElabReflection

public export
data Consumption : Type where
  Consuming : Consumption
  Unknown : Consumption

[SemigroupSequenceConsumption] Semigroup Consumption where
  Consuming <+> Consuming = Consuming
  Consuming <+> Unknown = Consuming
  Unknown <+> Consuming = Consuming
  Unknown <+> Unknown = Unknown

[SemigroupAlternateConsumption] Semigroup Consumption where
  Consuming <+> Consuming = Consuming
  Consuming <+> Unknown = Unknown
  Unknown <+> Consuming = Unknown
  Unknown <+> Unknown = Unknown

public export
data ParseError : e -> Type where
  ErrorEmpty : ParseError e
  ErrorNotEmpty : ParseError e
  Error : e -> ParseError e

-- c: Consumption
-- e: Error
-- t: Token
-- m: Monad
-- a: return value
public export
data GrammarT : (c : Consumption) -> e -> t -> m -> (a : Type) -> Type where
  Return : (value : a) ->
           GrammarT Unknown e t m a
  Fail : (error : ParseError e) ->
         GrammarT Unknown e t m a
  End : GrammarT Unknown e t m ()
  Consume : GrammarT Consuming e t m t
  Sequence : (gx : GrammarT cx e t m a) ->
             (gf : a -> GrammarT cf e t m b) ->
             GrammarT ((<+>) @{SemigroupSequenceConsumption} cx cf) e t m b
  Alternate : (gx : GrammarT cx e t m a) ->
              (gy : Lazy (GrammarT cy e t m a)) ->
              GrammarT ((<+>) @{SemigroupAlternateConsumption} cx cy) e t m a

export
Functor m => Functor (GrammarT c e t m) where
  map f g = case g of
    Return value => Return $ f value
    Fail error => Fail error
    End => Sequence End (Return . f)
    Consume => Consume `Sequence` (Return . f)
    Sequence gx gf => Sequence gx $ map f . gf
    Alternate g1 g2 => Alternate (map f g1) (map f g2)

(<*>) : Applicative m =>
        (gf : GrammarT cx e t m (a -> b)) ->
        (gx : GrammarT cf e t m a) ->
        GrammarT ((<+>) @{SemigroupSequenceConsumption} cx cf) e t m b
(<*>) gf gx = Sequence gf $ \ f => map f gx

(<|>) : Applicative m =>
        (gx : GrammarT cx e t m a) ->
        (gy : Lazy (GrammarT cy e t m a)) ->
        GrammarT ((<+>) @{SemigroupAlternateConsumption} cx cy) e t m a
(<|>) = Alternate

(>>=) : Monad m =>
        (gx : GrammarT cx e t m a) ->
        (gf : a -> GrammarT cf e t m b) ->
        GrammarT ((<+>) @{SemigroupSequenceConsumption} cx cf) e t m b
(>>=) = Sequence

export
parse : List t -> GrammarT c e t m a -> (Either (ParseError e) a, List t)
parse l p = case p of
  Return value => (Right value, l)
  Fail error => (Left error, l)
  End => case l of
    [] => (Right (), l)
    x :: xs => (Left ErrorNotEmpty, l)
  Consume => case l of
    [] => (Left ErrorEmpty, l)
    x :: xs => (Right x, xs)
  Sequence gx gf => case parse l gx of
    (Left gxError, gxL) => (Left gxError, gxL)
    (Right gxValue, gxL) => parse gxL $ gf gxValue
  Alternate gx gy => case parse l gx of
    (Right gxValue, gxL) => (Right gxValue, gxL)
    (Left gxError, gxL) => parse l gy
