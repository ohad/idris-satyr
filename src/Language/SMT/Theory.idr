module Language.SMT.Theory

import public Language.SMT.Signature
import public Language.SMT.Term

public export
record Theory where
  constructor MkTheory
  sig : Signature
  sortDescription ,
  funDescription  ,
  definition      ,
  -- Spec seems to say these are terms, but to me it looks like these
  -- are strings
  values          ,
  notes
    : String
  -- TODO: attributes

public export
record Logic where
  constructor MkLogic
  theory : Theory
  language ,
  extensions ,
  values ,
  notes : String
