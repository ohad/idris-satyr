module Language.SMT.Theory.Combination

import Language.SMT.Signature
import Data.Vect

parameters (sigs : List Signature)
  public export
  SortName : SortNameType
  SortName n = (sig : Signature
             ** pos : sig `Elem` sigs
             ** sig.SortName n)

  LiftSortName : {sig : Signature} ->
                 (pos : sig `Elem` sigs) -> sig.SortName n -> SortName n
  LiftSortName pos s = (sig ** pos ** s)
  LiftBoolOrSortName : {sig : Signature} ->
                 (pos : sig `Elem` sigs) -> BoolOr sig.SortName n -> BoolOr SortName n
  LiftBoolOrSortName pos Bool = Bool
  LiftBoolOrSortName pos (Just s) = Just (LiftSortName pos s)

  LiftSortNames : {sig : Signature} ->
                 (pos : sig `Elem` sigs) ->
                 Vect n (k : Nat ** BoolOr sig.SortName k) ->
                 Vect n (k : Nat ** BoolOr     SortName k)
  LiftSortNames pos = map $ \(k ** s) => (k ** LiftBoolOrSortName pos s)

  LiftSort : {sig : Signature} ->
             (pos : sig `Elem` sigs) -> sig.sort params -> (SortName).Sort params
  LiftSorts : Functor f =>
              {sig : Signature} ->
              (pos : sig `Elem` sigs) -> f (sig.sort params) -> f ((SortName).Sort params)

  LiftSort pos (Para var) = Para var
  LiftSort pos (Sort f xs) = Sort (LiftBoolOrSortName pos f)
                                $ LiftSorts pos xs
  LiftSorts pos xs = map (LiftSort pos) xs

  public export
  data ConName : FunNameType SortName where
    Con : forall ty . (pos : sig `Elem` sigs) -> sig.ConName {n} tys kty ->
      (0 fordArgs : tys' === LiftSortNames pos tys) =>
      (0 fordType : ty' = (kty.fst ** LiftBoolOrSortName pos kty.snd)) =>
      ConName {n} tys' ty'
{-
  --LiftCon : (pos : sig `Elem` sigs) -> sig.ConName

  public export
  ConCover : ConCoverType ConName
  ConCover (sig ** pos ** ty) =
    let Element tys pos' = sig.ConCover ty
    in  Element (map (\case
           Evidence tys' c =>
             Evidence (LiftSorts pos tys')
                      $ Con pos c) tys)
             $ \case
              (Evidence tys' $ c') =>
                (let 0 u = pos' (Evidence (map (?h18) tys') ?h199)
                in ?h19_0)
  FunName : FunNameType SortName
  SelName : SelNameType ConName
  TesterName : SelNameType ConName


  public export
  Combine : Signature
  Combine = MkSignature
    { SortName
    , ConName
    , ConCover
    , FunName
    , SelName = ?hh189
    , TesterName = ?h189781
    }
-}
