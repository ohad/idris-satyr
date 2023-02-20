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
data Segment : Signature -> Type where
  Nil : Segment sig
  (::) : (xtype : Binding sig) -> (xi : Segment sig) -> Segment sig

public export
(<><) : Context sig -> Segment sig -> Context sig
gamma <>< [] = gamma
gamma <>< (xtype :: xi) = (gamma :< xtype) <>< xi

public export
data Var : Context sig -> sig.sort [] -> Type where
  Here : Var (gamma :< (x :! ty)) ty
  There : Var gamma ty -> Var (gamma :< xtype) ty

namespace Segment
  public export
  data Var : Segment sig -> sig.sort [] -> Type where
    Here : Var ((x :! ty) :: xi) ty
    There : Var gamma ty -> Var (xtype :: gamma) ty

  public export
  data All : (xi : Segment sig) -> ((ty : sig.sort []) -> Var xi ty -> Type) -> Type where
    Nil : All [] p
    (::) : (0 p : (ty' : sig.sort []) -> Var {sig} ((x :! ty) :: xi) ty' -> Type) ->
      p ty (Segment.Here) ->
      All xi (\ty',pos => p ty' (There pos)) -> All ((x :! ty) :: xi) ?h2

public export
data Term : {sig : Signature} -> Context sig -> sig.sort [] -> Type where
  AVar : Var gamma ty -> Term gamma ty
  (@@) : (f : Symbol sig arity ty) -> All (Term gamma) arity ->
         Term {sig} gamma ty
  Exists, Forall : (xi : Segment sig) -> Term gamma' ty ->
    (0 ford : gamma' = gamma <>< xi) =>
    Term gamma ty
  Let : (xi : Segment sig) -> All xi (\ty',pos => Term gamma ty') ->
    Term gamma' ty ->
    (0 ford : gamma' = gamma <>< xi) =>
    Term gamma ty
