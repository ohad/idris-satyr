module Language.SMT.Term

import Language.SMT.Signature

import Data.Vect.Elem
import Data.Vect.Quantifiers

import Language.SMT.SExp

infix 3 :!

public export
record Binding (sig : Signature) where
  constructor (:!)
  name : String
  type : sig.sort []

public export
data Context : Signature -> Type where
  Lin : Context sig
  (:<) : (gamma : Context sig) -> Binding sig -> Context sig

public export
Segment : Nat -> Signature -> Type
Segment n sig = Vect n (Binding sig)

public export
(<><) : Context sig -> Segment n sig -> Context sig
gamma <>< [] = gamma
gamma <>< (xtype :: xi) = (gamma :< xtype) <>< xi

public export
data Var : Context sig -> sig.sort [] -> Type where
  Here : Var (gamma :< (x :! ty)) ty
  There : Var gamma ty -> Var (gamma :< xtype) ty

namespace Segment
  data Var : Segment n sig -> sig.sort [] -> Type where
    Here : Var ((x :! ty) :: xi) ty
    There : Var gamma ty -> Var (xtype :: gamma) ty

  public export
  data All : (xi : Segment n sig) -> ((ty : sig.sort []) -> Var xi ty -> Type) -> Type where
    Nil : All [] p
    (::) : (0 p : (ty' : sig.sort []) -> Var {sig} ((x :! ty) :: xi) ty' -> Type) ->
      p ty (Segment.Here) ->
      All xi (\ty',pos => p ty' (There pos)) -> All ((x :! ty) :: xi) ?h2

-- TODO: include booleans

indexFinAll : {0 xs : Vect n a} -> (i : Fin n) -> All p xs -> p (index i xs)
indexFinAll FZ (prf :: _) = prf
indexFinAll (FS i) (_ :: prfs) = indexFinAll i prfs

zipWithAll : (xs : Vect n a) -> {0 ys : Vect n b} ->
             (prfs : All p ys) ->
             (g : (i : Fin n) -> q (f (index i xs) (index i ys))) ->
             All q (zipWith f xs ys)
zipWithAll [] [] g = []
zipWithAll (x :: xs) (z :: zs) g = g 0 :: zipWithAll xs zs (\i => g $ FS i)

vectUncurry : (xs : Vect n a) -> All p xs -> Vect n (x : a ** p x)
vectUncurry [] [] = []
vectUncurry (x :: xs) (prf :: prfs) = (x ** prf) :: vectUncurry xs prfs

public export
forget : {xs : List a} -> All (const b) xs -> Vect (length xs) b
forget [] = []
forget (y :: ys) = y :: forget ys

public export
data Pattern : Segment n sig -> (ty : sig.sort []) -> Type where
  CatchAll : {0 sig : Signature} ->
    {0 ty : sig.sort []} ->
    (x : String) -> Pattern {sig} [x :! ty] ty

  Case     : {0 sig : Signature} -> forall n, k, tys, ty, args, seg, s.
             {0 seg : Segment n sig} ->
             (c : sig.ConName {n} params tys s) ->
             (subst : sig.TySubst params []) ->
             (vars : Vect n String) ->
             (0 fordTy : args === forget subst) =>
             (0 fordSegment : seg === zipWith (\x,u => x :! u.subst subst)
                                        vars tys
             ) =>
            Pattern {sig} seg (Sort (Just s) args)

public export
data Term : {sig : Signature} -> Context sig -> sig.sort [] -> Type where
  AVar : Var gamma ty -> Term gamma ty
  (@@) : (f : Symbol sig params arity ty) -> (theta : sig.TySubst params []) ->
         All (\x => Term gamma $ x.subst theta) arity ->
         (0 fordSort : ty' === ty.subst theta) =>
         Term {sig} gamma ty'
  Exists, Forall : (xi : Segment n sig) -> Term gamma' ty ->
    (0 ford : gamma' = gamma <>< xi) =>
    Term gamma ty
  Let : (xi : Segment n sig) -> All xi (\ty',pos => Term gamma ty') ->
    Term gamma' ty ->
    (0 ford : gamma' = gamma <>< xi) =>
    Term gamma ty
  Match : Term gamma ty ->
    List (p : Pattern seg ty ** Term (gamma <>< seg) ty') ->
    -- Cover!
    Term gamma ty'

export
ListSExpRep (Binding sig) where
  toSExpList (name :! type) = [Literal name, ?h1]
  fromSExpList [Literal name, mtype] = Just (name :! ?h2)  -- TODO: deal with parsing sort
  fromSExpList _ = Nothing
