module Language.SMT.Theory.ArrayEx

public export
data SortName : Nat -> Type where
  Array : SortName 2
