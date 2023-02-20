module Language.SMT.Command

import Language.SMT.SExp
import Language.SMT.Response

data Command : Type where
  -- 4.1.1. Restarting and terminating

  ||| resets the solver completely to the state it had after it was
  ||| started and before it started reading commands.
  Reset ,
  ||| instructs the solver to exit
  Exit  : Command
  {- TODO:
  SetLogic : Command
  SetOption : Command
  -}

  -- 4.2.2. Modifying the assertion stack

  ||| pushes n empty assertion levels onto the assertion stack. 2 If n
  ||| is 0, no assertion levels are pushed.
  Push : (n : Nat) -> Command

  ||| n is smaller than the number of assertion levels in the stack,
  ||| pops the n most-recent assertion levels from the stack.
  ||| When n = 0, no assertion levels are popped.
  |||
  ||| The first assertion level, which is not created by a push
  ||| command, cannot be popped.
  Pop  : (n : Nat) -> Command

  ||| Removes from the assertion stack all assertion levels beyond the
  ||| first one. In addition, it removes all assertions from the first
  ||| assertion level.
  |||
  ||| Declarations and definitions resulting from the set-logic
  ||| command are unaffected (because they are global).
  |||
  ||| Similarly, if the option :global-declarations has value true at
  ||| the time the command is executed, then all declarations and
  ||| definitions remain unaffected. Note that any information set
  ||| with set-option commands is preserved in any case.
  ResetAssertions : Command

  -- 4.2.3. Introducing new symbols

  {- TODO:
  DeclareSort ,
  DefineSort ,
  DeclareFun ,
  DeclareConst ,
  DeclareDatatypes ,
  DeclareDatatype  -- Sugar
  DefineFun        -- Sugar
  DefineFunsRec ,
  DefineFunRec  -- Sugar?

  -}

  -- 4.2.4. Asserting and inspecting formulae

  {- TODO:

  Assert ,
  GetAssertions
  -}

  -- 4.2.5. Checking for satisfiability

  {- TODO:

  CheckSat -- Sugar
  CheckSatAssuming
  -}

  -- 4.2.6. Inspecting models

  -- 4.2.7. Inspecting proofs

  -- 4.2.8. Inspecting settings

  -- 4.2.9. Script information

SExpRep Command where
  toSExp = ?h2
  fromSExp = ?h1

(.responseType) : Command -> Type
--(Reset).responseType = ?responseType_rhs

_.responseType = WithSuccess Void
