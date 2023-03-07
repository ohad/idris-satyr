||| Scheme-like `cond` construct
module Control.Cond

public export
||| `Cond [(bs, xs)] y` represents:
|||
||| Case
|||   b1 => x1
|||   b2 => x2
|||   ...
|||   bn => xn
|||   else => y
Cond : List (Lazy Bool, Lazy a) -> Lazy a -> a
Cond [] elseBranch = elseBranch
Cond ((x, y) :: xs) elseBranch =
  if x
  then y
  else Cond xs elseBranch

public export
||| `Cond [(bs, xs)] y` represents:
|||
||| Case
|||   b1 => x1
|||   b2 => x2
|||   ...
|||   bn => xn
|||   else => y
CondMaybe : List (Lazy (Maybe c), c -> a) -> Lazy a -> a
CondMaybe [] elseBranch = elseBranch
CondMaybe ((mx, f) :: xs) elseBranch =
  case mx of
    Just x  => f x
    Nothing => CondMaybe xs elseBranch

infix 2 ==>
public export
(==>) : Lazy a -> Lazy b -> (Lazy a, Lazy b)
(==>) = curry id
