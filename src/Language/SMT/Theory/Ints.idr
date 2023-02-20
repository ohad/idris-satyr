module Language.SMT.Theory.Ints

import Language.SMT.Signature

import Data.Vect.Quantifiers
import Data.List
import Data.List.Quantifiers

{-
 :sorts ((Int 0))

 :funs ((NUMERAL Int)
        (- Int Int)                 ; negation
        (- Int Int Int :left-assoc) ; subtraction
        (+ Int Int Int :left-assoc)
        (* Int Int Int :left-assoc)
        (div Int Int Int :left-assoc)
        (mod Int Int Int)
        (abs Int Int)
        (<= Int Int Bool :chainable)
        (<  Int Int Bool :chainable)
        (>= Int Int Bool :chainable)
        (>  Int Int Bool :chainable)
       )
-}


public export
data SortName : Nat -> Type where
  IntName : SortName 0

public export
SInt : (SortName).Sort params
SInt = Sort (Just IntName) []

data FunName : forall n. (0 params : List String) ->
    (Vect n ((SortName).Sort params)) -> (SortName).Sort params -> Type
    where
  NEG ,
  ABS : FunName [] [SInt] SInt
  PLUS ,
  MULT ,
  SUB  ,
  DIV  : FunName [] [SInt, SInt] SInt
  LEQ ,
  LT  ,
  GEQ ,
  GT  : FunName [] [SInt, SInt] SBool
