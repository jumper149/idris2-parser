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
-- a: return value
public export
data Grammar : (c : Consumption) -> e -> t -> (a : Type) -> Type where
  Return : (value : a) ->
           Grammar Unknown e t a
  Fail : (error : ParseError e) ->
         Grammar Unknown e t a
  End : Grammar Unknown e t ()
  Consume : Grammar Consuming e t t
  Sequence : (gx : Grammar cx e t a) ->
             (gf : a -> Grammar cf e t b) ->
             Grammar ((<+>) @{SemigroupSequenceConsumption} cx cf) e t b
  Alternate : (gx : Grammar cx e t a) ->
              (gy : Lazy (Grammar cy e t a)) ->
              Grammar ((<+>) @{SemigroupAlternateConsumption} cx cy) e t a

export
Functor (Grammar c e t) where
  map f g = case g of
    Return value => Return $ f value
    Fail error => Fail error
    End => Sequence End (Return . f)
    Consume => Consume `Sequence` (Return . f)
    Sequence gx gf => Sequence gx $ map f . gf
    Alternate g1 g2 => Alternate (map f g1) (map f g2)

(<*>) : (gf : Grammar cx e t (a -> b)) ->
        (gx : Grammar cf e t a) ->
        Grammar ((<+>) @{SemigroupSequenceConsumption} cx cf) e t b
(<*>) gf gx = Sequence gf $ \ f => map f gx

(<|>) : (gx : Grammar cx e t a) ->
        (gy : Lazy (Grammar cy e t a)) ->
        Grammar ((<+>) @{SemigroupAlternateConsumption} cx cy) e t a
(<|>) = Alternate

(>>=) : (gx : Grammar cx e t a) ->
        (gf : a -> Grammar cf e t b) ->
        Grammar ((<+>) @{SemigroupSequenceConsumption} cx cf) e t b
(>>=) = Sequence

export
parse : List t -> Grammar c e t a -> (Either (ParseError e) a, List t)
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
