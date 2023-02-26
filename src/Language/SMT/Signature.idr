module Language.SMT.Signature

import public Data.Vect
import public Data.List.Elem
import public Data.List.Quantifiers
import public Data.Vect.Quantifiers
import public Data.Cover
import public Data.DPair

public export
data BoolOr : (Nat -> Type) -> (n : Nat) -> Type where
  Bool : BoolOr p 0
  Just : a n -> BoolOr a n


public export
data (.Sort) : (Nat -> Type) -> List String -> Type where
  Para : (0 var : String) -> {auto pos : var `Elem` params} -> p.Sort params
  Sort : {0 params : List String} ->
         (f : BoolOr p n) ->
         Vect n (p.Sort params) ->
         p.Sort params

public export 0
SortNameType : Type
SortNameType = Nat -> Type

public export 0
FunNameType : SortNameType -> Type
FunNameType sort = forall n.
    Vect n (k : Nat ** BoolOr sort k) -> (k : Nat ** BoolOr sort k)  -> Type

public export 0
ConCoverType : FunNameType sort -> Type
ConCoverType {sort} conName = forall n. (s : sort n) ->
    Cover (Exists $ \tys : Vect n (k : Nat ** BoolOr sort k) =>
             conName tys (n ** Just s))

public export 0
SelNameType : FunNameType sort -> Type
SelNameType {sort} conName = forall n.
    {0 arity : Vect n (k : Nat ** BoolOr sort k)} ->
    {0 s : sort n} ->
    conName arity (n ** Just s) ->
    (Fin n) -> Type

public export
record Signature where
  constructor MkSignature
  SortName : SortNameType
  -- All of these will be singleton types :D
  FunName, ConName : FunNameType SortName
  ConCover : ConCoverType ConName
  SelName, TesterName : SelNameType ConName

public export
(.sort) : Signature -> List String -> Type
sig.sort = (sig.SortName).Sort


public export
(.tySubst) : (sig : Nat -> Type) -> (paramsSrc, paramsTgt : List String) -> Type
sig.tySubst paramsSrc paramsTgt = All (const $ sig.Sort paramsTgt) paramsSrc

public export
(.TySubst) : (sig : Signature) -> (paramsSrc, paramsTgt : List String) -> Type
sig.TySubst = sig.SortName.tySubst


public export
SBool : p.Sort params
SBool = Sort Bool []

public export total
(.subst) : p.Sort paramsSrc -> p.tySubst paramsSrc paramsTgt -> p.Sort paramsTgt
(Para var {pos}).subst theta = indexAll pos theta
(Sort f xs).subst theta = Sort f (map (\ty =>  assert_total $
                                               ty.subst theta) xs)

public export
TypeInstantiation : (sig : Signature) ->
  (params : List String) ->
  (k : Nat ** BoolOr sig.SortName k) ->
  Type
TypeInstantiation sig params ks = Vect ks.fst (sig.sort params)

public export
Instantiation : (sig : Signature) ->
  Vect n (k : Nat ** BoolOr sig.SortName k) -> (k : Nat ** BoolOr sig.SortName k)  ->
  (params : List String) -> Type
Instantiation sig tys ty params =
  (All (TypeInstantiation sig params) tys, TypeInstantiation sig params ty)

public export
data Symbol : (sig : Signature) -> {n : Nat} ->
  Vect n (k : Nat ** BoolOr sig.SortName k) ->
  (k : Nat ** BoolOr sig.SortName k) -> Type where
  Fun : (f : sig.FunName {n} arity tyName) ->
    Symbol sig arity tyName
  Con : sig.ConName arity sort -> Symbol sig arity sort
  Sel : sig.SelName {s,arity} con i ->
        Symbol sig [sort] ty
  Tes : sig.TesterName {s, arity} con i ->
        Symbol sig [sort] (_ ** Bool)
