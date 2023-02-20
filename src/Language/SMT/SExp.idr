||| SMT-LIB compatible representation of SExpressions
module Language.SMT.SExp

import Data.List
import Data.Maybe

%default total

public export
data SExp : Type where
  Literal : String -> SExp
  AList   : List SExp -> SExp

public export
interface SExpRep a where
  toSExp : a -> SExp
  fromSExp : SExp -> Maybe a

public export
SExpRep Void where
  toSExp _ impossible

  fromSExp = const Nothing
