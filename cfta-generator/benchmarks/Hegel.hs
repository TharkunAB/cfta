{-# LANGUAGE OverloadedStrings #-}

{- | Hegel's evaluation: each refinement-typed query, with the reduction steps
of the paper's ablations.

The parent runs each query in a child process with a heap limit and a time
limit. Each row of the CSV gives the query, the outcome (@solved@,
@unsolved@, @timeout@, or @crash@), the size of the solutions, the seconds,
the entailment queries, the states before and after reduction at the last
size, and the first solution.

With no arguments, it runs one small query of five groups with 60 seconds and
a heap of 2 GB each, so that @cabal bench@ stays short.

> hegel [all | -P | -S | -All] [seconds] [heap]
> hegel --query NAME REDUCTION seconds
> hegel --trace NAME REDUCTION seconds
> hegel --generator NAME
-}
module Main (main) where

import Data.List (find)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)
import System.Environment (getArgs, getExecutablePath)
import System.Exit (ExitCode (..))
import System.IO (hFlush, stdout)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Text.Printf (printf)

import Data.CFTA.Formula (Name (..), Sort (..))
import qualified Data.CFTA.Gen.Refinement as LTAGen
import Data.CFTA.Gen.Synthesis.HegelBenchmarks
import Data.CFTA.Gen.Synthesis.Liquid
import Data.CFTA.Index (everyRank)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Timeout)
import qualified Data.CFTA.Term as Term

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["--query", name, reduction, seconds] -> runQuery False name reduction (read seconds)
        ["--trace", name, reduction, seconds] -> runQuery True name reduction (read seconds)
        ["--generator", name] -> generatorQuery name
        [] -> runSuite "all" 60 "2G" smoke
        [reduction] -> runSuite reduction 180 "8G" liquidBenchmarks
        [reduction, seconds] -> runSuite reduction (read seconds) "8G" liquidBenchmarks
        [reduction, seconds, heap] -> runSuite reduction (read seconds) heap liquidBenchmarks
        _ -> fail "usage: hegel [all | -P | -S | -All] [seconds] [heap]"

-- | The reduction steps of a variant of the paper.
reductionOf :: String -> Reduction
reductionOf variant = case variant of
    "-P" -> Reduction False True
    "-S" -> Reduction True False
    "-All" -> Reduction False False
    _ -> Reduction True True

-- | One small query of five groups.
smoke :: [LiquidBenchmark]
smoke =
    [ benchmark
    | benchmark <- liquidBenchmarks
    , liquidName benchmark `elem` ["RevApp1", "Nth_Incr1", "LookRange1", "MapDouble1", "ApplyList1"]
    ]

-- | Run each query in a child process and print one row for each.
runSuite :: String -> Int -> String -> [LiquidBenchmark] -> IO ()
runSuite variant seconds heap benchmarks = do
    executable <- getExecutablePath
    putStrLn "query,outcome,size,seconds,queries,undecided,states,reduced,solution"
    mapM_ (runChild executable) benchmarks
  where
    runChild executable benchmark = do
        let name = Text.unpack $ liquidName benchmark
        (code, output, _) <-
            readProcessWithExitCode
                executable
                ["--query", name, variant, show seconds, "+RTS", "-M" <> heap, "-RTS"]
                ""
        putStrLn $ case (code, lines output) of
            (ExitSuccess, row : _) -> row
            _ -> name <> ",crash,,,,,,,"
        hFlush stdout

{- | The time limit of one solver query, in milliseconds. A query about
quantified refinements can run long; at the limit it counts as undecided.
-}
queryLimit :: Int
queryLimit = 100

-- | Synthesize one query and print its row.
runQuery :: Bool -> String -> String -> Int -> IO ()
runQuery trace name variant seconds = case find ((== Text.pack name) . liquidName) liquidBenchmarks of
    Nothing -> fail $ "no query " <> name
    Just benchmark ->
        withZ3Timeout
            queryLimit
            [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
            []
            $ \solver -> do
                start <- getMonotonicTime
                let options =
                        defaultOptions
                            { optionReduction = reductionOf variant
                            , optionMaximumSize = liquidBound benchmark
                            , optionTrace = trace
                            , optionConditionals = liquidConditionals benchmark
                            }
                result <- timeout (seconds * 1000000) $ synthesize solver options (liquidLibrary benchmark) (liquidQuery benchmark)
                end <- getMonotonicTime
                putStrLn $ case result of
                    Nothing -> name <> ",timeout,,,,,,,"
                    Just (Left err) -> name <> ",error,,,,,,," <> show err
                    Just (Right outcome) ->
                        let Statistics size states reduced queries undecided = outcomeStatistics outcome
                            solution = case outcomeSolutions outcome of
                                first : _ -> renderTerm first
                                [] -> ""
                            outcomeName = if null (outcomeSolutions outcome) then "unsolved" else "solved" :: String
                         in printf
                                "%s,%s,%d,%.3f,%d,%d,%d,%d,%s"
                                name
                                outcomeName
                                size
                                (end - start)
                                queries
                                undecided
                                states
                                reduced
                                (show solution)

{- | The goal automaton of a query as a generator, compiled with the solver:
the count of its solutions, a round trip from each rank to its term and
back, and the solutions in rank order.
-}
generatorQuery :: String -> IO ()
generatorQuery name = case find ((== Text.pack name) . liquidName) liquidBenchmarks of
    Nothing -> fail $ "no query " <> name
    Just benchmark ->
        withZ3Timeout
            queryLimit
            [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
            []
            $ \solver -> do
                let options = defaultOptions{optionMaximumSize = liquidBound benchmark, optionConditionals = liquidConditionals benchmark}
                result <- synthesize solver options (liquidLibrary benchmark) (liquidQuery benchmark)
                case result of
                    Left err -> fail err
                    Right Outcome{outcomeAutomaton = Nothing} -> putStrLn $ name <> ": no goal automaton"
                    Right Outcome{outcomeAutomaton = Just automaton} -> do
                        compiled <- LTAGen.compileWith solver (LTAGen.fromAutomaton automaton)
                        generator <- either (fail . show) pure compiled
                        total <- either (fail . show) pure (LTAGen.cardinality generator)
                        solutions <- either (fail . show) pure (LTAGen.values generator)
                        let roundTrips = and [(LTAGen.termAt generator rank >>= LTAGen.rankOf generator) == Right rank | rank <- everyRank total]
                        printf "%s: %s ranks, rank round trip: %s\n" name (show total) (show roundTrips)
                        mapM_ (putStrLn . ("solution: " <>) . renderTerm) (concatMap Term.subForest solutions)
