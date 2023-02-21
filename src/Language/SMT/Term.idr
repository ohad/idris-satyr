module Language.SMT.Term

import Language.SMT.Signature

import Data.Vect.Quantifiers

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
data Segment : Nat -> Signature -> Type where
  Nil : Segment 0 sig
  (::) : (xtype : Binding sig) -> (xi : Segment n sig) -> Segment (S n) sig

public export
(<><) : Context sig -> Segment n sig -> Context sig
gamma <>< [] = gamma
gamma <>< (xtype :: xi) = (gamma :< xtype) <>< xi

public export
data Var : Context sig -> sig.sort [] -> Type where
  Here : Var (gamma :< (x :! ty)) ty
  There : Var gamma ty -> Var (gamma :< xtype) ty

namespace Segment
  public export
  data Var : Segment n sig -> sig.sort [] -> Type where
    Here : Var ((x :! ty) :: xi) ty
    There : Var gamma ty -> Var (xtype :: gamma) ty

  public export
  data All : (xi : Segment n sig) -> ((ty : sig.sort []) -> Var xi ty -> Type) -> Type where
    Nil : All [] p
    (::) : (0 p : (ty' : sig.sort []) -> Var {sig} ((x :! ty) :: xi) ty' -> Type) ->
      p ty (Segment.Here) ->
      All xi (\ty',pos => p ty' (There pos)) -> All ((x :! ty) :: xi) ?h2

public export
data Pattern : sig.ConName params tys ty -> Segment n sig -> Type where
  CatchAll : Pattern {ty} c [x :! ty]
  {- I am here
  Case     : (c : sig.ConName params tys ty) ->
             (vars : Vect n String) ->
             (0 ford :
             Pattern c seg
  -}

public export
data Term : {sig : Signature} -> Context sig -> sig.sort [] -> Type where
  AVar : Var gamma ty -> Term gamma ty
  (@@) : (f : Symbol sig arity ty) -> All (Term gamma) arity ->
         Term {sig} gamma ty
  Exists, Forall : (xi : Segment n sig) -> Term gamma' ty ->
    (0 ford : gamma' = gamma <>< xi) =>
    Term gamma ty
  Let : (xi : Segment n sig) -> All xi (\ty',pos => Term gamma ty') ->
    Term gamma' ty ->
    (0 ford : gamma' = gamma <>< xi) =>
    Term gamma ty
