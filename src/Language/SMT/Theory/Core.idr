module Language.SMT.Theory.Core

import Language.SMT.Signature
import Data.Vect.Quantifiers
import Data.List
import Data.List.Quantifiers


%default total

{-
:funs ((true Bool)
        (false Bool)
        (not Bool Bool)
        (=> Bool Bool Bool :right-assoc)
        (and Bool Bool Bool :left-assoc)
        (or Bool Bool Bool :left-assoc)
        (xor Bool Bool Bool :left-assoc)
        (par (A) (= A A Bool :chainable))
        (par (A) (distinct A A Bool :pairwise))
        (par (A) (ite Bool A A A))
       )
-}

public export
SortName : Nat -> Type
SortName n = Void

public export
data FunName : FunNameType SortName
    where
  NOT : FunName [] [SBool] SBool

  IMPLIES ,
  AND     ,
  OR      ,
  XOR     : FunName []    [ SBool   , SBool   ] SBool
  EQ,NEQ  : FunName ["x"] [ Para "x", Para "x"] SBool
  ITE     : FunName ["x"] [ Para "x", Para "x"] (Para "x")

public export
Core : Signature
Core = MkSignature
  { SortName
  , FunName
  , ConName = \_,_,_ => Void
  , ConCover   = \_ => \case _ impossible
  , SelName    = \_ => \case _ impossible
  , TesterName = \_ => \case _ impossible
  }
