||| A monad for collecting SAT constraints
module Language.SAT.Monad

import Data.SnocList
import Data.DPair
import Data.Nat
import Language.SAT.Dimacs
import Data.List.Elem

import Data.SnocList.Quantifiers
import Data.List.Quantifiers

-- Ought to go in Data.List.Quantifiers
public export
(++) : {0 xs,ys : List a} -> All p xs -> All p ys -> All p (xs ++ ys)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

mapWithElem : ((0 x : a) -> x `Elem` xs -> p x -> q x) -> All p xs -> All q xs
mapWithElem f [] = []
mapWithElem f (prf :: prfs) = f _ Here prf :: mapWithElem (\0 x, y, z => f x (There y) z) prfs

Inj : (m, n : Nat) -> Type
Inj m n = m `LTE` n

InjInto,InjFrom : (n : Nat) -> Type
InjInto n = (k : Nat ** k `Inj` n)
InjFrom m = (k : Nat ** m `Inj` k)


(.dom) : InjInto n -> Nat
(.dom) rho = rho.fst

(.cod) : InjFrom n -> Nat
(.cod) rho = rho.fst

ConstraintVals : Type
ConstraintVals = ClauseOver Nat

ConstraintWell : (n : Nat) -> ConstraintVals -> Type
ConstraintWell n vals = All (\bi => snd bi `LTE` n) vals

ConstraintsVals : Type
ConstraintsVals = SnocList ConstraintVals

ConstraintsWell : (n : Nat) -> ConstraintsVals -> Type
ConstraintsWell n constraints = All (\clause => ConstraintWell n clause) constraints

Constraints : (n : Nat) -> Type
Constraints n = ConstraintsVals `Subset` (ConstraintsWell n)



||| A state monad
-- Can try to use a writer monad instead, but I think that will mean
-- we need to move variable names around, making computations less
-- efficient. This way variable names stay the same.
record SAT a where
  constructor MkSAT
  runWith : {0 n : Nat} -> Constraints n ->
    Exists {type = InjFrom n} (\rho => (a, Constraints rho.cod))

pure : a -> SAT a
pure x = MkSAT $ \constraints => Evidence (_ ** reflexive) (x, constraints)

(>>=) : SAT a -> (a -> SAT b) -> SAT b
xs >>= f = MkSAT $ \constraints =>
  let Evidence rho1 (x, cs) = xs.runWith constraints
      Evidence rho2 (y, ds) = (f x).runWith cs
  in Evidence (_ ** transitive rho1.snd rho2.snd)
              (y, Element (cs.fst ++ ds.fst)
                $ mapProperty (\prf =>
                    mapWithElem
                      (\x, x_in_xs, prf => transitive prf rho2.snd)
                      prf) cs.snd
                  ++
                  ds.snd)
