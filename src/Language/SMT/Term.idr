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

public export
data Term : {sig : Signature} -> Context sig -> sig.sort [] -> Type where
  AVar : Var gamma ty -> Term gamma ty
  (@@) : (f : Symbol sig arity ty) -> All (Term gamma) arity ->
         Term {sig} gamma ty
