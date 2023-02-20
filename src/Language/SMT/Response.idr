module Language.SMT.Response

import Language.SMT.SExp

public export
data Response : Type -> Type where
  Success : a -> Response a
  Unsupported : Response a
  Error : String -> Response a

public export
SExpRep a => SExpRep (Response a) where
  toSExp (Success x) = toSExp x
  toSExp Unsupported = Literal $ "unsupported"
  toSExp (Error msg) = AList $ map Literal ["error", msg]

  fromSExp (Literal "unsupported") = Just Unsupported
  fromSExp (AList [Literal "error", Literal msg]) =
    Just $ Error msg
  fromSExp (Literal x) = do
    y <- fromSExp {a} (Literal x)
    pure $ Success y
  fromSExp _ = Nothing

public export
data WithSuccess a = PureSuccess | Just a

public export
SExpRep a => SExpRep (WithSuccess a) where
  toSExp PureSuccess = Literal "success"
  toSExp (Just x) = toSExp x

  fromSExp (Literal "success") = Just PureSuccess
  fromSExp x = fromSExp x
