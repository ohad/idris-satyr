module Language.SMT.Signature

import public Data.Vect
import public Data.List.Elem
import Data.Vect.Quantifiers
import Data.List
import Data.List.Quantifiers

%hide Data.List.sort

public export
data BoolOr : (Nat -> Type) -> (n : Nat) -> Type where
  Bool : BoolOr p 0
  Just : a n -> BoolOr a n

infix 3 ~>

public export
(~>) : (sub, sup : List String) -> Type
sub ~> sup = All (`Elem` sup) sub

public export
data (.Sort) : (Nat -> Type) -> List String -> Type where
  Para : (0 var : String) -> {auto pos : var `Elem` params} -> p.Sort params
  Sort : (f : BoolOr p n) ->
         {0 paramsSrc : Vect n (List String)} ->
         All p.Sort paramsSrc ->
         (All (~> params) paramsSrc) =>
         p.Sort params

public export
record Signature where
  constructor MkSignature
  SortName : Nat -> Type
  -- All of these will be singleton types :D
  FunName, ConName : forall n. (0 params : List String) ->
    (Vect n ((SortName).Sort params)) -> (SortName).Sort params -> Type
  SelName, TesterName : forall n, params .
    {0 arity : Vect n ((SortName).Sort params)} ->
    {0 sort : (SortName).Sort params} ->
    ConName params arity sort ->
    (Fin n) -> Type

public export
(.sort) : Signature -> List String -> Type
sig.sort = (sig.SortName).Sort

public export
SBool : p.Sort params
SBool = Sort Bool []

public export
data Symbol : (sig : Signature) -> {params : List String} ->
  (Vect n ((sig.SortName).Sort params)) -> (sig.SortName).Sort params -> Type where
  Fun : sig.FunName params arity sort -> Symbol sig arity sort
  Con : sig.ConName params arity sort -> Symbol sig arity sort
  Sel : sig.SelName {sort,arity} con i ->
        {auto 0 ford : index i arity = ty} ->
        Symbol sig [sort] ty
  Tes : sig.TesterName {sort, arity} con i ->
        Symbol sig [sort] SBool
