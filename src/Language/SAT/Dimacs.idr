module Language.SAT.Dimacs

import public Data.Vect
import Data.String
import Data.List
import Data.List.Quantifiers
import System
import System.File
import System.Random
import System.File.Process

public export
record Header where
  constructor MkHeader
  variables : Nat
  clauses   : Nat

public export
ClauseOver : Type -> Type
ClauseOver a = List (Bool, a)

public export
Clause : (vars : Nat) -> Type
Clause vars = ClauseOver (Fin vars)

public export
record Dimacs (header : Header) where
  constructor MkDimacs
  clauses : Vect header.clauses $ Clause header.variables

serialiseHeader : Header -> String
serialiseHeader header = "p cnf \{show header.variables} \{show header.clauses}"

serialiseClause : {vars : Nat} -> Clause vars -> String
serialiseClause xs
  = ( concat
    $ intersperse " "
    $ map (\(b, v) =>
      (if b then "" else "-") ++ (show $ S $ cast v))
          xs)
    ++ " 0"

serialiseLines : {header : Header} -> Dimacs header -> List String
serialiseLines dimacs =
  serialiseHeader
    header ::
    (toList $
      map (serialiseClause {vars = header.variables})
                           dimacs.clauses)

export
serialise : {header : Header} -> Dimacs header -> String
serialise = unlines . serialiseLines

-- smart constructor
public export
CNF : {m,n : Nat} ->
  (f : Vect n (Bool, Fin n) -> Vect m (Clause n)) ->
  Dimacs (MkHeader n m)
CNF f = MkDimacs $ f $ map (True,) range

public export
¬ : (Bool, Fin n) -> (Bool, Fin n)
¬ x = (not $ fst x, snd x)

export
||| x , ¬ x: Unsat
Ex1 : Dimacs ?
Ex1 = CNF $ \[x,y,z] =>
  [ [x]
  , [¬ x]
  ]

Ex2 : Dimacs ?
Ex2 = CNF $ \[x,y,z] =>
  [ [x, y]
  , [¬ x]
  ]

Ex3 : Dimacs ?
Ex3 = CNF $ \[x,y,z] =>
  [ [x, ¬ y, z]
  , [y]
  ]

export
(.header) : {header : Header} -> Dimacs header -> Header
_.header = header

public export
Satisfaction : Header -> Type
Satisfaction header = Vect header.variables (Maybe Bool)

showSatisfaction : {header : Header} -> Satisfaction header
  -> String
showSatisfaction xs =
  let width : Nat = cast $ log (cast header.variables) in
  foldr (\u,v => u ++ " " ++ v)
    "" $ toList $ zipWith (\i,mb => case mb of
    Just b => (if b then "" else "~") ++
      "x\{padLeft width ' ' $ show $ finToNat i}"
    Nothing => "")
    Fin.range xs

public export
data Response : (header : Header) -> Type where
  IsSat : Satisfaction header -> Response header
  Unsat : Response header
  Dunno : Response header

export
{header : Header} -> Show (Response header) where
  show (IsSat xs) = """
    Satisfiable:
    \{showSatisfaction {header} xs}
    """
  show Unsat = "Unsat"
  show Dunno = "Unknown"

parseFin : (n : Nat) -> String -> Maybe (Bool, Fin n)
parseFin n str = do
  i <- parseInteger str
  let Just result = integerToFin (i-1) n
  | Nothing => do {Just (False, !(integerToFin (-1 - i) n))}
  pure (True, result)

parseZ3Satisfaction : {header : Header} -> List String ->
  Maybe $ Satisfaction header
parseZ3Satisfaction strs = do
  fins <- traverse (parseFin header.variables) strs
  pure $ tabulate $ \i =>
    map fst $ find ((== i) . snd) fins

parseZ3Result :
  {header : Header} ->
  String -> Maybe $ Response header
parseZ3Result str = case map toLower $ lines $ trim str of
  "sat" :: sats =>
    map IsSat $ parseZ3Satisfaction $ words $ unlines sats
  "unsat" :: _ => pure Unsat
  _ => pure Dunno

Resources : Type
Resources = List $ IO ()

cleanup : Resources -> IO ()
cleanup resources = do {_ <- traverse id resources; pure ()}

z3Invocation : (filename : String) -> String
z3Invocation filename = "z3 sat.cardinality.solver=false -dimacs -file:\{filename}"

export
SAT : {header : Header} -> Dimacs header -> IO (Response header)
-- I don't know how to pipe into z3, so let's use a temporary file
SAT dimacs = do
  let resources = []
  (filename', 0) <- run "mktemp"
  | _ => pure Dunno
  let filename = trim filename'
  let resources = do {_ <- removeFile filename; pure ()} :: resources
  let str = serialise dimacs
  Right file <- openFile filename WriteTruncate
  | Left _ => do {putStrLn "failed to open file for writing"; cleanup resources; pure Dunno}
  let resources' = closeFile file :: resources
  Right () <- fPutStrLn file str
  | Left _ => do {putStrLn "failed to write contents to file"; cleanup resources'; pure Dunno}
  closeFile file
  (resultStr, 0) <- run $ z3Invocation filename
  | _ => do {cleanup resources; pure Dunno}
  cleanup resources
  let Just result = parseZ3Result resultStr
  | Nothing => pure Dunno
  pure result
