import Data.Fin
import Data.DPair

record InvertLTE (m, n : Nat) where
  constructor MkInvertLTE
  0 pred : Nat
  eqProof : n === S pred
  lteProof : LTE m pred

invertLTE : LTE (S m) n -> InvertLTE m n
invertLTE (LTESucc p) = MkInvertLTE _ Refl p

fastWeakenLTE : Fin m -> (0 _ : LTE m n) -> Fin n
fastWeakenLTE FZ p =
  let 0 inv = invertLTE p in
  rewrite inv.eqProof in FZ
fastWeakenLTE (FS k) p =
  let 0 inv = invertLTE p in
  rewrite inv.eqProof in
  FS (fastWeakenLTE k inv.lteProof)

specWeakenLTE : (i : Fin m) -> (prf : LTE m n) -> weakenLTE i prf = fastWeakenLTE i prf
specWeakenLTE FZ (LTESucc x) = Refl
specWeakenLTE (FS i) (LTESucc prf) = cong FS $ specWeakenLTE i prf
