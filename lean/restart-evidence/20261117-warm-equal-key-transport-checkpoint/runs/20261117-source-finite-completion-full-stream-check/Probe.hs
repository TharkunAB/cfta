{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Observe one genuine source query. See Note [Opaque self-application].
module Main (main) where

import Data.CFTA.Gen.Synthesis
    ( Encoding (FirstOrder)
    , Library (..)
    , Program (..)
    , Query (..)
    , Space (..)
    , Type (..)
    , rawSearchSpace
    , reduceWithOrder
    , renderProgram
    , solutionsOfSize
    )
import qualified Data.CFTA.Enumeration as Enumeration
import Data.CFTA.Symbol (Symbol, symbolText)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import System.Environment (getArgs)
import System.Exit (die)
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdout)
import Text.Read (readMaybe)

{- Note [Opaque self-application]
The source library contains type schemes and names. It evaluates no component.
Each use of fix has its own type instance. The inner application fix fix forces
an instance variable t to equal both s and s -> s. No finite type satisfies this.
The outer k leaves this argument type unconstrained by the ground result Int.
A matching output is a candidate counterexample. The same typed run and its
residuals must be reviewed before any source correctness claim is made.
-}

-- | The original accepted syntax, with one group for each component.
sourceLibrary :: Library
sourceLibrary =
    Library
        [ ("fix", TFun (TFun b b) b, ["fix"])
        , ("k", TFun a int, ["k"])
        ]
        []
        []
        FirstOrder
  where
    a = TVar "a"
    b = TVar "b"
    int = TCons "Int" []

-- | The ground source query has no term arguments.
sourceQuery :: Query
sourceQuery = Query [] (TCons "Int" [])

-- | Both source programs have three component leaves.
sourceSize :: Int
sourceSize = 3

-- | Candidate and finite control. This list does not filter the worker.
targets :: [(String, Program, Bool)]
targets =
    [ ("infinite_type_candidate", App (Var "k") (App (Var "fix") (Var "fix")), False)
    , ("finite_control", App (Var "k") (App (Var "k") (Var "fix")), True)
    ]

-- | Decode the exact FirstOrder shapes used by Synthesis.toProgram.
programOf :: Term Symbol -> Program
programOf term = case (Term.rootLabel term, Term.subForest term) of
    ("app", [_, _, function, argument]) -> App (programOf function) (programOf argument)
    ("filter", [_, candidates]) -> programOf candidates
    (name, _) -> Var (symbolText name)

-- | Observe a list prefix. Only an actual empty tail establishes exhaustion.
scan :: Int -> (a -> Program) -> (a -> String) -> [a] -> IO ()
scan limit decode showActual = go limit (0 :: Int) []
  where
    go !remaining !count found stream
        | remaining == 0 = finish count False found
        | otherwise = case stream of
            [] -> finish count True found
            actual : rest -> do
                let program = decode actual
                putStrLn ("output.index=" ++ show count ++ "; output.program=" ++ renderProgram program)
                putStrLn ("output.actual=" ++ showActual actual)
                let matched = [name | (name, expected, _) <- targets, program == expected, name `notElem` found]
                mapM_ (reportMatch count actual) matched
                go (remaining - 1) (count + 1) (matched ++ found) rest
    reportMatch index actual name = do
        putStrLn ("match.name=" ++ name)
        putStrLn ("match.output_index=" ++ show index)
        putStrLn ("match.actual=" ++ showActual actual)
    finish count exhausted found = do
        putStrLn ("observed.outputs=" ++ show count)
        putStrLn ("observed.exhaustion=" ++ show exhausted)
        mapM_ (report exhausted found) targets
    report exhausted found (name, _, finiteExpected) = do
        let status
                | name `elem` found = "present"
                | exhausted = "absent_after_exhaustion"
                | otherwise = "unobserved_at_output_limit"
        putStrLn ("result.name=" ++ name ++ " status=" ++ status ++ " finite_type_expected=" ++ show finiteExpected)

-- | Run one original route. Root supplies the external process limits.
main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    args <- getArgs
    case args of
        [route, limitText]
            | Just limit <- readMaybe limitText
            , limit > 0 -> do
                putStrLn ("route=" ++ route ++ "; status=observation_only")
                putStrLn ("library=" ++ show sourceLibrary)
                putStrLn ("query=" ++ show sourceQuery ++ "; source_size=" ++ show sourceSize)
                mapM_ (\(name, program, finiteExpected) ->
                    putStrLn ("target=" ++ name ++ "; source=" ++ renderProgram program ++ "; finite_type_expected=" ++ show finiteExpected)) targets
                putStrLn "phase=source_construction_and_enumeration_begin"
                let raw = rawSearchSpace sourceLibrary sourceQuery sourceSize
                case route of
                    "public" -> scan limit id show (solutionsOfSize sourceLibrary sourceQuery sourceSize)
                    "typed-reduced" ->
                        let space = reduceWithOrder raw
                         in scan limit (programOf . fst) show (Enumeration.runsBy (spaceOrder space) "Mu" (spaceNode space))
                    "typed-raw" -> scan limit (programOf . fst) show (Enumeration.runsBy (const 0) "Mu" raw)
                    _ -> die "Route must be public, typed-reduced, or typed-raw."
        _ -> die "Usage: Probe.hs public|typed-reduced|typed-raw OUTPUT_LIMIT"
