module Language.SMT.Logic.UFNIA

import Language.SMT.Theory
import Language.SMT.Theory.Core
import Language.SMT.Theory.Ints
import Language.SMT.Theory.Combination

public export
Theories : List Signature
Theories = [Core, Ints.Sig]

public export
Sig : Signature
Sig = Combine Theories

-- Move these somewhere
public export
(.index) : (xs : List a) -> Fin (length xs) -> a
[].index _ impossible
(y :: xs).index FZ = y
(y :: xs).index (FS i) = xs.index i

public export
(.position) : (xs : List a) -> (i : Fin (length xs)) -> xs.index i `Elem` xs
[].position _impossible
(x :: xs).position FZ = Here
(x :: xs).position (FS i) = There (xs.position i)
{-
public export
SInt : ((Ints.Sig).SortName).Sort params
SInt = LiftSort _ (_.position 1) (Ints.SInt)
-}
public export
theory : Theory
theory = MkTheory
  { sig = UFNIA.Sig
  -- TODO: populate with actual strings
  , sortDescription = ""
  , funDescription  = ""
  , definition      = ""
  , values          = ""
  , notes           = ""
  }


public export
UFNIA : Logic
UFNIA = MkLogic
  { theory = Ints
  , name = "UFNIA"
  , language = ""
  , extensions = ""
  , values = ""
  , notes = ""
  }
