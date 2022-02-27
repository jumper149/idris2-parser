module Control.Grammar.Core

import Generics.Derive

%language ElabReflection

public export
data ParseError : e -> Type where
  ErrorEmpty : ParseError e
  ErrorNotEmpty : ParseError e
  Error : e -> ParseError e

-- c: Guaranteed Consumption
-- e: Error
-- t: Token
-- a: return value
public export
data Grammar : (c : Bool) -> e -> t -> (a : Type) -> Type where
  Return : (value : a) ->
           Grammar False e t a
  Fail : (error : ParseError e) ->
         Grammar c e t a
  Catch : (failing : Grammar cf e t a) ->
          (catching : ParseError e -> Grammar cc e t a) ->
          Grammar (cx && cf) e t a
  End : Grammar False e t ()
  Consume : Grammar True e t t
  Sequence : (gx : Grammar cx e t a) ->
             (gf : a -> Grammar cf e t b) ->
             Grammar (cx || cf) e t b
  Alternate : (gx : Grammar cx e t a) ->
              (gy : Lazy (Grammar cy e t a)) ->
              Grammar (cx && cy) e t a

public export
Functor (Grammar c e t) where
  map f g = case g of
    Return value => Return $ f value
    Fail error => Fail error
    Catch failing catching => Catch (map f failing) (map f . catching)
    End => Sequence End (Return . f)
    Consume => Consume `Sequence` (Return . f)
    Sequence gx gf => Sequence gx $ map f . gf
    Alternate g1 g2 => Alternate (map f g1) (map f g2)

public export
return : a -> Grammar False e t a
return = Return

public export
(<*>) : (gf : Grammar cx e t (a -> b)) ->
        (gx : Grammar cf e t a) ->
        Grammar (cx || cf) e t b
(<*>) gf gx = Sequence gf $ \ f => map f gx

public export
(>>=) : (gx : Grammar cx e t a) ->
        (gf : a -> Grammar cf e t b) ->
        Grammar (cx || cf) e t b
(>>=) = Sequence

public export
(>>) : (gx : Grammar cx e t a) ->
       (gy : Grammar cf e t b) ->
       Grammar (cx || cf) e t b
gx >> gy = gx >>= const gy

public export
fail : ParseError e -> Grammar c e t a
fail = Fail

public export
catch : (failing : Grammar cf e t a) ->
        (catching : ParseError e -> Grammar cc e t a) ->
        Grammar (cx && cf) e t a
catch = Catch

public export
(<|>) : (gx : Grammar cx e t a) ->
        (gy : Lazy (Grammar cy e t a)) ->
        Grammar (cx && cy) e t a
(<|>) = Alternate

public export
end : Grammar False e t ()
end = End

public export
consume : Grammar True e t t
consume = Consume

public export
parse : List t -> Grammar c e t a -> (Either (ParseError e) a, List t)
parse l p = case p of
  Return value => (Right value, l)
  Fail error => (Left error, l)
  Catch failing catching => case parse l failing of
    (Left error, _) => parse l $ catching error
    success@(Right _, _) => success
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
