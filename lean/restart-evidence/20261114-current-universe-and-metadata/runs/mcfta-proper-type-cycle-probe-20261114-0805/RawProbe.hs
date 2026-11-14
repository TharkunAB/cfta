{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Probe the raw source root before reduction and refolding.
module Main (main) where

import Control.Monad (when)
import Data.CFTA.Constraint (Constraint)
import qualified Data.CFTA.Enumeration as E
import Data.CFTA.Gen.Synthesis
    ( Encoding (FirstOrder)
    , Library (..)
    , Program (..)
    , Query (..)
    , Space (..)
    , Type (..)
    , rawSearchSpace
    , programsIn
    , renderProgram
    , (~>)
    )
import Data.CFTA.Symbol (Symbol, symbolText)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import Data.Text (Text)
import System.Environment (getArgs)
import System.Exit (die)
import System.IO (BufferMode (LineBuffering), hFlush, hSetBuffering, stdout)

-- | A source AST and its independent finite-HM membership expectation.
data Candidate = Candidate
    { candidateName :: String
    , candidateProgram :: Program
    , finiteHMExpected :: Bool
    }

-- | One library, query, source size, and finite list of candidate ASTs.
data ProbeCase = ProbeCase
    { caseName :: String
    , caseLibrary :: Library
    , caseQuery :: Query
    , caseSize :: Int
    , caseCandidates :: [Candidate]
    }

-- | The observed prefix count, exhaustion flag, and matched candidate ASTs.
data Summary = Summary !Integer !Bool [Program]

-- | Build singleton component groups with the ordinary first-order encoding.
mkLibrary :: [(Text, Type)] -> Library
mkLibrary entries = Library [(name, typ, [name]) | (name, typ) <- entries] [] [] FirstOrder

-- | Select one supported source-generated case.
lookupCase :: String -> Maybe ProbeCase
lookupCase name = case name of
    "FPROPER" -> Just $ ProbeCase name
        (mkLibrary [("need", (a ~> TCons "F" [a]) ~> bool), ("i", b ~> b), ("liftF", c ~> TCons "F" [c])])
        (Query [] bool) 2
        [ Candidate "proper_constructor_cycle" (App (Var "need") (Var "i")) False
        , Candidate "finite_constructor_control" (App (Var "need") (Var "liftF")) True
        ]
    "BOUND" -> Just $ ProbeCase name boundLibrary boundQuery 3
        [Candidate "bound_self_application" (App (Var "sink") (App (Var "bound") (Var "bound"))) False]
    "SKI" -> Just $ ProbeCase name skiLibrary (Query [] bool) 4
        [ Candidate "ski_self_application" (App (Var "sink") (App (App (Var "s") (Var "i")) (Var "i"))) False
        , Candidate "ski_finite_control" (App (Var "sink") (App (App (Var "s") (Var "k")) (Var "k"))) True
        ]
    "POLY" -> Just $ ProbeCase name (mkLibrary [("i", a ~> a)]) (Query [] (bool ~> bool)) 2
        [Candidate "polymorphic_identity_control" (App (Var "i") (Var "i")) True]
    _ -> Nothing
  where
    a = TVar "a"
    b = TVar "b"
    c = TVar "c"
    bool = TCons "Bool" []
    sinkType = a ~> bool
    boundLibrary = mkLibrary [("sink", sinkType)]
    boundQuery = Query [("bound", a ~> b)] bool
    skiLibrary = mkLibrary
        [ ("sink", sinkType)
        , ("s", (a ~> b ~> c) ~> (a ~> b) ~> a ~> c)
        , ("i", a ~> a)
        , ("k", a ~> b ~> a)
        ]

-- | Decode exactly as Synthesis.toProgram at source lines 963-966.
-- This function only observes the typed run. It does not run enumeration.
programOfTypedTerm :: Term Symbol -> Program
programOfTypedTerm term = case (Term.rootLabel term, Term.subForest term) of
    ("app", [_, _, function, argument]) -> App (programOfTypedTerm function) (programOfTypedTerm argument)
    ("filter", [_, candidates]) -> programOfTypedTerm candidates
    (symbol, _) -> Var (symbolText symbol)

-- | Flush phase progress before source construction or enumeration starts.
progress :: String -> IO ()
progress message = putStrLn message >> hFlush stdout

-- | Print one bounded value and state whether its encoding is complete.
printBounded :: (Show a) => String -> a -> IO ()
printBounded label value = do
    let limit = 16384
        prefix = take (limit + 1) (show value)
    putStrLn $ label <> ".show_complete=" <> show (length prefix <= limit)
    putStrLn $ label <> "=" <> take limit prefix

-- | Scan each public program at most once. Retain only candidate ASTs.
scanPublic :: [Candidate] -> [Program] -> IO Summary
scanPublic candidates = go 0 []
  where
    go !count !found programs
        | all ((`elem` found) . candidateProgram) candidates = pure $ Summary count False found
        | otherwise = case programs of
            [] -> pure $ Summary count True found
            program : rest -> do
                let matching = filter ((== program) . candidateProgram) candidates
                    firstMatch = not (null matching) && program `notElem` found
                    !newFound = if firstMatch then program : found else found
                when firstMatch $ do
                    putStrLn $ "public.match=" <> show (map candidateName matching)
                    printBounded "public.ast" program
                    hFlush stdout
                go (count + 1) newFound rest

-- | Scan one raw typed-run stream and retain its exact first matched pairs.
-- At most one pair per candidate is printed. Oversized output is marked.
scanTyped :: [Candidate] -> [(Term Symbol, [(Constraint, Term Symbol)])] -> IO Summary
scanTyped candidates = go 0 []
  where
    go !count !found runs
        | all ((`elem` found) . candidateProgram) candidates = pure $ Summary count False found
        | otherwise = case runs of
            [] -> pure $ Summary count True found
            run@(term, _) : rest -> do
                let program = programOfTypedTerm term
                    matching = filter ((== program) . candidateProgram) candidates
                    firstMatch = not (null matching) && program `notElem` found
                    !newFound = if firstMatch then program : found else found
                when firstMatch $ do
                    putStrLn $ "typed.match=" <> show (map candidateName matching)
                    printBounded "typed.ast" program
                    printBounded "typed.same_run_term_and_residuals" run
                    hFlush stdout
                go (count + 1) newFound rest

-- | Report presence, or absence only after the observed stream is exhausted.
printSummary :: String -> [Candidate] -> Summary -> IO ()
printSummary phase candidates (Summary count exhausted found) = do
    putStrLn $ phase <> ".scanned=" <> show count
    putStrLn $ phase <> ".exhausted=" <> show exhausted
    mapM_ report candidates
    hFlush stdout
  where
    report candidate = do
        let present = candidateProgram candidate `elem` found
            status
                | present = "present"
                | exhausted = "absent_after_exhaustion"
                | otherwise = "unobserved"
        putStrLn $ phase <> ".candidate=" <> show (candidateName candidate)
            <> " status=" <> status
            <> " finite_hm_expected=" <> show (finiteHMExpected candidate)

-- | Evaluate programsIn and the typed run on one raw root, once per route.
runCase :: ProbeCase -> IO ()
runCase config = do
    progress $ "case=" <> caseName config
    putStrLn $ "source_size=" <> show (caseSize config)
    printBounded "library" (caseLibrary config)
    printBounded "query" (caseQuery config)
    mapM_ (printBounded "candidate.ast" . candidateProgram) (caseCandidates config)
    mapM_ (printBounded "candidate.source" . renderProgram . candidateProgram) (caseCandidates config)
    let space = Space (rawSearchSpace (caseLibrary config) (caseQuery config) (caseSize config)) (const 0)
    printBounded "raw.root_reachesConstrainedMu" (E.reachesConstrainedMu (spaceNode space))
    progress "phase=public.programsIn.raw.begin"
    publicSummary <- scanPublic (caseCandidates config) $
        programsIn space
    printSummary "public" (caseCandidates config) publicSummary
    progress "phase=typed.raw.begin; evaluation=separate_from_public"
    typedSummary <- scanTyped (caseCandidates config) $
        E.runsBy (spaceOrder space) "Mu" (spaceNode space)
    printSummary "typed" (caseCandidates config) typedSummary
    progress "case_complete=True; observations_only=True; partial_type_scope=retained"

-- | Run exactly one named case in this process.
main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    args <- getArgs
    case args of
        [name] | Just config <- lookupCase name -> runCase config
        _ -> die "Usage: probe FPROPER|BOUND|SKI|POLY"
