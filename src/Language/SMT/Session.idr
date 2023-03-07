module Language.SMT.Session

import Language.SMT.SExp
import Language.SMT.Response
import Language.SMT.Theory
import Language.SMT.Command

import System
import System.File
import System.File.Process

import Control.Monad.Trans
import Control.Monad.Either

import Data.String

-- TODO: erase
import Language.SMT.Logic.UFNIA

public export
record SessionState where
  constructor B
  mlogic : Maybe Logic
  context : maybe Unit (\logic => Context logic.theory.sig) mlogic
  level : Nat

public export
data Session : (prec, post : SessionState) -> Type -> Type where
  -- Try to use the minimal level that works
  Exit : Session pre (B Nothing () 0) ()
  SetInfo : Session state state ()
  SetLogic : (logic : Logic) ->
    Session pre (B (Just logic) [<] 0) ()
  Push : (n : Nat) -> Session pre (B pre.mlogic pre.context (n + pre.level)) ()
  Pop : forall mlogic, context, level.
        (k : Nat) -> Session (B mlogic context (k + level)) (B mlogic context level) ()
  DeclareConst :
   forall logic, context, level.
   (xty : Binding logic.theory.sig) ->
   Session (B (Just logic) context level)
           (B (Just logic) (context :< xty)  level) ()
  Assert :
    forall logic, context, level.
    Term context SBool ->
    Session (B (Just logic) context level)
            (B (Just logic) context level)
            ()
  CheckSAT :
    forall logic, context, level.
    Session (B (Just logic) context level)
            (B (Just logic) context level)
            (Command.CheckSAT).responseType
  Pure : a -> Session prec post a
  (>>=) : Session pre mid a -> ((x : a) -> Session mid post b) ->
    Session pre post b

public export
pure : a -> Session prec post a
pure = Pure

public export
(>>) : Session pre mid () -> Lazy (Session mid post b) -> Session pre post b
x >> y = x >>= (const y)

record LL where
  constructor L
  connected : Bool
  z3_in,z3_out : if connected then File else ()

public export
data SessionError : Type where
  CannotCreateTempDir ,
  CannotCreatePipe    : (errcode : Int) -> (msg : String) -> SessionError
  FailedToSetupPipeIn  ,
  FailedToSetupPipeOut : (msg : String) -> SessionError
  Z3Interaction ,
  FailedToInitializeZ3 ,
  FailedToFinalizeZ3   : (msg : String) -> SessionError
  UnexpectedZ3Response : (response : String) -> SessionError
  FailCleanup : (errcode : Int) -> (msg : String) -> SessionError
  Disconnected : SessionError
  FailExecute : (cmd : String) -> (err : String) -> SessionError

LowLevelSession : Type -> Type
LowLevelSession a = (state : LL) => EitherT SessionError IO a

exec : Session prec post a -> LowLevelSession a
exec x @{state@(L {connected=False} {})} = left Disconnected
exec Exit
  @{state@(L {connected=True} {})}
  = do
  Right () <- fPutStrLn state.z3_in "(exit)"
  | Left err => left $ FailedToFinalizeZ3 $ show err
  pure ()
exec CheckSAT               -- Weird that we have to match on z3_out like this
  @{state@(L {connected=True, z3_out, z3_in} {})}
  = do
  Right () <- fPutStrLn state.z3_in "(check-sat)"
  | Left err => left $ FailExecute "check-sat" $ show err
  fflush z3_in
  let Right res = map trim !(fGetLine z3_out)
  | Left err => left $ FailExecute "check-sat" $ show err
  case res of
    "sat"     => pure SAT
    "unsat"   => pure UNSAT
    "unknown" => pure UNKNOWN
    str         => left $ FailExecute "check-sat" str
exec SetInfo
  @{state@(L {connected=True} {})}
  = pure ()--?exec_rhs_3
exec (SetLogic logic)
  @{state@(L {connected=True, z3_in, z3_out} {})}
    = do
    Right () <- fPutStrLn state.z3_in "(set-logic \{logic.name})"
    | Left err => left $ FailExecute "set-logic: \{logic.name}" $ show err
    fflush z3_in
    -- todo: use parser
    let Right "success" = map trim !(fGetLine z3_out)
    | Right str => left $ FailExecute "set-logic: \{logic.name}" $ str
    | Left err => left $ FailExecute "set-logic: \{logic.name}" $ show err
    pure ()
exec (Push n)
  @{state@(L {connected=True} {})}
    = pure () --?exec_rhs_5
exec (Pop k)
  @{state@(L {connected=True} {})}
    = pure () --?exec_rhs_6
exec (DeclareConst xty)
  @{state@(L {connected=True} {})}
  = pure () --?exec_rhs_7
exec (Assert x)
  @{state@(L {connected=True} {})}
  = pure () --?exec_rhs_8
exec (Pure x)
  @{state@(L {connected=True} {})}
  = pure x
exec (x >>= f)
  @{state@(L {connected=True} {})}
  = exec x >>= (\i => exec $ f i)


modusPonens : (state : LL) => LowLevelSession a -> EitherT SessionError IO a
modusPonens @{state} f = f @{state}


runLLSession : LowLevelSession a -> IO (Either SessionError a)
runLLSession f = runEitherT {e = SessionError, m = IO} $ do
  -- Set-up the z3 server, using an intermediate named-pipe
  -- Create the pipe in a temporary directory
  let z3IO = "IdrisSatyrZ3process"
  (z3IOdirRaw,0) <- lift $ run "mktemp -d \{z3IO}.XXX"
  | (str, errcode) => left $ CannotCreateTempDir errcode str
  let z3IOdir = trim z3IOdirRaw
  let z3FIFO_out = "\{z3IOdir}/\{z3IO}.out"
  (_, 0) <- lift $ run "mkfifo \{z3FIFO_out}"
  | (str, errcode) => left $ CannotCreatePipe errcode str
  -- Set up Z3 in a separate process, and connect it to the pipe
  Right z3_out <- popen "cat < \{z3FIFO_out} &" Read
  | Left err => left $ FailedToSetupPipeOut $ show err
  Right z3_in <- popen "z3 -smt2 -in > \{z3FIFO_out} " WriteTruncate
  | Left err => left $ FailedToSetupPipeIn $ show err
  Right () <- lift $ fPutStrLn z3_in "(set-option :print-success true)"
  | Left err => left $ FailedToSetupPipeIn $ show err
  fflush z3_in
  -- TODO: use SExp parser to extract Success PureSuccess out.
  let Right "success" = map trim !(lift $ fGetLine z3_out)
  | Right other => left $ UnexpectedZ3Response other
  | Left err    => left $ FailedToInitializeZ3 $ show err
  let sessionState : LL = L True z3_in z3_out
  result <- f
  Right () <- lift $ fPutStrLn z3_in "(exit)"
  | Left err => left $ FailedToFinalizeZ3 $ show err
  0 <- pclose z3_in
  | n => left $ FailedToFinalizeZ3
              $ "Error (\{show n}) while closing input pipe."
  0 <- lift $ pclose z3_out
  | n => left $ FailedToFinalizeZ3
              $ "Error (\{show n}) while closing Z3 output pipe."
  (_, 0) <- run "rm -rf \{z3IOdir}"
  | (str, errcode) => left $ FailCleanup errcode
      "Error (\{show errcode}) while cleaning up named pipes: \{str}"
  pure result

z3Invocation : String
z3Invocation = "z3 -smt2 -in"

initialize : SessionState
initialize = B {mlogic = Nothing, context = (), level = 0}

testScript : IO ()
testScript = do
  Right res <- runLLSession $ exec {prec = initialize}$ do
    SetLogic UFNIA
    CheckSAT
  | Left err => putStrLn "Error!"
  putStrLn $ case res of
    SAT => "sat"
    UNSAT => "unsat"
    UNKNOWN => "unknown"
  pure ()


runScript : Session prec post () -> IO ()
runScript x = do
  --  (resultStr, 0) <- run $ z3Invocation filename
  ?runScript_rhs
