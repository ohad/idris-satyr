module Data.Cover

import Data.DPair
import Data.List.Elem

public export
Cover : Type -> Type
Cover a = Subset (List a) $ \xs => (x : a) -> x `Elem` xs
