import Data.Vect
import Data.List.Elem
import Data.List.Quantifiers
import Data.Vect.Quantifiers
import Data.DPair

infix 3 ~>

-- consider upstreaming these to the stdlib

public export
(~>) : (sub, sup : List String) -> Type
sub ~> sup = All (`Elem` sup) sub

-- Make fully compositional?

indexFinElem : (xs : List a) -> Fin (length xs) -> Exists (\x => x `Elem` xs)
indexFinElem [] _ impossible
indexFinElem (x :: xs) FZ = Evidence x Here
indexFinElem (x :: xs) (FS i) = Evidence _ (There (indexFinElem xs i).snd)

-- identity at runtime!
public export
massage : {0 xs : Vect n a} -> All (f . g) xs -> All f (map g xs)
massage [] = []
massage (x :: xs) = x :: massage xs

0 anyRecall : {0 xs : Vect n a} -> Any p xs -> a
anyRecall {xs = x :: xs} (Here  prf) = x
anyRecall {xs = x :: xs} (There pos) = anyRecall pos

anyIndex : {0 xs : Vect n a} -> (pos : Any p xs) -> p (anyRecall pos)
anyIndex (Here  prf) = prf
anyIndex (There pos) = anyIndex pos

anyAll : {0 xs : Vect n a} -> (pos : Any p xs) -> All q xs -> q (anyRecall pos)
anyAll (Here prf) (x :: xs) = x
anyAll (There pos) (x :: xs) = anyAll pos xs

mapByAny : {0 xs : Vect n a} ->
  ((pos : Any p xs) -> q (anyRecall pos)) -> All p xs -> All q xs
mapByAny f [] = []
mapByAny f (prf :: xs) = (f $ Here prf) :: mapByAny (\pos => f $ There pos) xs
