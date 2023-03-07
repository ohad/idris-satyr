||| SMT-LIB compatible representation of SExpressions
module Language.SMT.SExp

import Data.List
import Data.Maybe

%default total

public export
record Decimal where
  constructor (.)
  integral : Integer
  fractional : Nat

public export
data SExp : Type where
  ANumeral : Nat -> SExp
  ADecimal : Decimal -> SExp
  Literal : String -> SExp
  AList   : List SExp -> SExp

public export
interface SExpRep a where
  toSExp : a -> SExp
  fromSExp : SExp -> Maybe a

public export
interface ListSExpRep a where
  toSExpList : a -> List SExp
  fromSExpList : List SExp -> Maybe a

public export
SExpRep Void where
  toSExp _ impossible

  fromSExp = const Nothing
