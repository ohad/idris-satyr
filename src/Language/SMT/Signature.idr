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
{-
namespace UserFacing
  public export
  data ExtSort : List String -> SortNameType -> Type where
    Bool : ExtSort params sort
    Just : {k : Nat} -> sort k -> ExtSort params sort
    Para : (0 s : String) -> (pos : s `Elem` params) => ExtSort params sort
-}
public export 0
FunNameType : SortNameType -> Type
FunNameType sort = forall n.
    (params : List String) ->
    Vect n (sort.Sort params) ->
    (sort.Sort params) -> Type

public export 0
ConNameType : SortNameType -> Type
ConNameType sort = forall n.
    (params : List String) ->
    Vect n (sort.Sort params) ->
    (sort $ length params) -> Type


public export 0
ConstructorType : SortNameType -> Type
ConstructorType sort = forall n.
    (params : List String) ->
    Vect n (sort.Sort params) ->
    (BoolOr sort n) -> Type


-- TODO: move to stdlib
public export
tabulateByElem : (xs : List a) -> ((0 x : a) -> x `Elem` xs -> b) -> Vect (length xs) b
tabulateByElem [] f = []
tabulateByElem (x :: xs) f = f x Here :: tabulateByElem xs (\0 y, z => f y (There z))

public export
(.conType) :
  {params : List String} ->
  (s : sort $ length params) ->
  (sort.Sort params)
s.conType = Sort (Just s) $ tabulateByElem params (\0 x, y => Para x)

public export
(.constructorType) :
  {params : List String} ->
  (s : BoolOr sort n) ->
  (sort.Sort params)



public export 0
ConCoverType : ConNameType sort -> Type
ConCoverType {sort} conName = forall n.
    (params : List String) -> (s : sort $ length params) ->
    Cover (Exists $ \tys : Vect n (sort.Sort params) =>
             conName params tys s)

public export 0
SelNameType : ConNameType sort -> Type
SelNameType {sort} conName = forall n. (params : List String) ->
    {0 arity : Vect n (sort.Sort params)} ->
    {0 s : sort $ length params} ->
    conName {n} params arity s ->
    (Fin n) -> Type

public export 0
TesterNameType : ConNameType sort -> Type
TesterNameType {sort} conName = forall n. (params : List String) ->
    {0 arity : Vect n (sort.Sort params)} ->
    {0 s : sort $ length params} ->
    conName {n} params arity s -> Type


public export
record Signature where
  constructor MkSignature
  SortName : SortNameType
  -- All of these will be singleton types :D
  FunName : FunNameType SortName
  ConName : ConNameType SortName
  ConCover : ConCoverType ConName
  SelName : SelNameType ConName
  TesterName : TesterNameType ConName

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
SBool : {sort : SortNameType} -> sort.Sort params
SBool = Sort Bool []

public export total
(.subst) : p.Sort paramsSrc -> p.tySubst paramsSrc paramsTgt -> p.Sort paramsTgt
(Para var {pos}).subst theta = indexAll pos theta
(Sort f xs).subst theta = Sort f (map (\ty =>  assert_total $
                                               ty.subst theta) xs)

-- Since _all_ theories ought to contain the booleans, we hard-code them:
public export
data (.Constructor) : (sig : Signature) -> ConstructorType (sig.SortName) where
  Prim : (c : sig.ConName params tys ty) ->
    sig.Constructor params tys (Just {n = length params} ty)
  True,False : (c : sig.ConName params tys ty) -> sig.Constructor params [] Bool
{-
public export
(.CoverType) : (sig : Signature) -> forall n.
    (params : List String) -> (s : BoolOr sig.SortName n) ->
    Type
sig.CoverType params Bool = Cover (Exists \tys => sig.Constructor params tys Bool )
sig.CoverType params (Just x) = ?h1_1
-}
--Cover (Exists $ \tys : Vect n (sig.sort params) =>
             --sig.Constructor params tys s)

public export
data Symbol : (sig : Signature) -> {n : Nat} -> (params : List String) ->
  (Vect n (sig.sort params)) ->
  (sig.sort params) -> Type where

  Fun : (f : sig.FunName params arity tyName) ->
    Symbol sig params arity tyName

  Con : (c : sig.Constructor params tys ty) ->
    Symbol sig params tys ?fty

  Sel : (c : sig.ConName {n} params tys sort) ->
        (sel : sig.SelName {n,s=sort,arity=tys} params c i) ->
        (0 fordArg : sort' === sort.conType) =>
        (0 fordSort : ty === index i tys) =>
        Symbol sig params [sort'] ty
  Tes : sig.TesterName {s, arity} params con ->
        Symbol sig params [sort] SBool
