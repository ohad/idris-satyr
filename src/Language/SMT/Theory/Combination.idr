module Language.SMT.Theory.Combination

import Language.SMT.Signature
import Data.Vect

public export
mapLemma : x `Elem` xs -> (f x) `Elem` (map f xs)
mapLemma Here = Here
mapLemma (There pos) = There $ mapLemma {f} pos


public export
SortName : (sigs : List Signature) -> SortNameType
SortName sigs n = (sig : Signature
             ** pos : sig `Elem` sigs
             ** sig.SortName n)
public export
LiftSortName : (sigs : List Signature) ->
               {sig : Signature} ->
               (pos : sig `Elem` sigs) -> sig.SortName n -> SortName sigs n
LiftSortName sigs pos s = (sig ** pos ** s)

public export
LiftBoolOrSortName :
  (sigs : List Signature) ->
  {sig : Signature} ->
  (pos : sig `Elem` sigs) ->
  BoolOr sig.SortName n -> BoolOr (SortName sigs) n
LiftBoolOrSortName sigs pos Bool = Bool
LiftBoolOrSortName sigs pos (Just s) = Just (LiftSortName sigs pos s)
{-
  public export
  LiftSortNames : {sig : Signature} ->
                 (pos : sig `Elem` sigs) ->
                 Vect n (k : Nat ** BoolOr sig.SortName k) ->
                 Vect n (k : Nat ** BoolOr     SortName k)
  LiftSortNames pos = map $ \(k ** s) => (k ** LiftBoolOrSortName pos s)
-}
public export
LiftSort :
  (sigs : List Signature) ->
  {sig : Signature} ->
  (pos : sig `Elem` sigs) -> sig.sort params -> (SortName sigs).Sort params

public export
LiftSorts : Functor f =>
  (sigs : List Signature) ->
  {sig : Signature} ->
 (pos : sig `Elem` sigs) -> f (sig.sort params) -> f ((SortName sigs).Sort params)
LiftSort sigs pos (Para var) = Para var
LiftSort sigs pos (Sort f xs) = Sort (LiftBoolOrSortName sigs pos f)
                              $ LiftSorts sigs pos xs
LiftSorts sigs pos xs = map (LiftSort sigs pos) xs

public export
data ConName : (sigs : List Signature) -> ConNameType (SortName sigs) where
    LiftCon : (pos : sig `Elem` sigs) ->
      sig.ConName {n} params tys ty ->
      forall tys',s.
      (0 fordArgs : tys' === LiftSorts {params} sigs pos tys) =>
      (0 fordSort : s === LiftSortName {n = length params} sigs pos ty) =>
      ConName sigs {n} params tys' s

public export
LiftClosedCon :
  (sigs : List Signature) ->
  (pos : sig `Elem` sigs) ->
  forall ty.
  (Exists $ \tys => sig.ConName {n} params tys ty) ->
  (Exists $ \tys' => ConName sigs {n} params tys'
                       (LiftSortName {n = length params} sigs pos ty))
LiftClosedCon sigs pos (Evidence tys c) =
    Evidence
      (LiftSorts sigs pos tys)
      (LiftCon pos c)

ConCover : (sigs : List Signature) -> ConCoverType (ConName sigs)
ConCover sigs params (sig ** pos ** s) =
    let Element tys cover = sig.ConCover params s
    in Element
         (map (LiftClosedCon sigs {params} pos) tys)
       $ \case
          (Evidence _ c@(
            LiftCon {sigs = sigs'}
             { ty = ty'
             , tys = rys
             , fordSort = Refl, fordArgs = Refl}
                      pos c'))
              => mapLemma $ cover (Evidence _ c')

public export
data FunName : (sigs : List Signature) -> FunNameType (SortName sigs) where
  LiftFun : forall sigs,params. (pos : sig `Elem` sigs) ->
    forall tys,ty.
    sig.FunName params tys ty ->
    forall s,tys'.
    (0 fordArgs : tys' === LiftSorts {f = Vect n, params} sigs pos tys) =>
    (0 fordSort : s === LiftSort sigs pos ty) =>
    FunName sigs params tys' s

public export
data SelName : (sigs : List Signature) -> SelNameType (ConName sigs) where
    LiftSel : (pos : sig `Elem` sigs) ->
      forall arity, s, c.
      {0 c : sig.ConName params arity s} ->
      sig.SelName {n,s,arity} params c i ->
      forall c'.
      (0 ford : c' === LiftCon pos c
               { tys = arity, ty = s
               , fordArgs = Refl, fordSort = Refl}) =>
      SelName sigs params {n, s = (sig ** pos ** s)} c' i

public export
data TesterName : (sigs : List Signature) -> TesterNameType (ConName sigs) where
  LiftTester : (pos : sig `Elem` sigs) ->
    forall n,arity, s.
    {0 c : sig.ConName {n} params arity s} ->
    sig.TesterName {n,s,arity} params c ->
    forall c', s', arity'.
    (0 fordSortName : s' === LiftSortName {n = length params} sigs pos s) =>
    (0 fordArgs : arity' === LiftSorts sigs pos arity) =>
    (0 ford : c' === LiftCon pos c
             { tys = arity
             , ty = s
             , fordArgs = Refl
             , fordSort = Refl}) =>
    TesterName sigs {n, arity = arity', s = s'} params ?hc

public export
Combine : (sigs : List Signature) -> Signature
Combine sigs = MkSignature
    { SortName   = SortName   sigs
    , ConName    = ConName    sigs
    , ConCover   = ConCover   sigs
    , FunName    = FunName    sigs
    , SelName    = SelName    sigs
    , TesterName = TesterName sigs
    }
