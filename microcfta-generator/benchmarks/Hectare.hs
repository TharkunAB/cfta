{-# LANGUAGE OverloadedStrings #-}

{- | Hectare's evaluation: each Hoogle+ query, searched size by size until
the expected solution appears.

The parent runs each query in a child process with a heap limit and a time
limit, so that a query that runs out of memory or time stops only itself.
Each row of the CSV gives the query, the outcome (@solved@, @unsolved@,
@timeout@, or @crash@), the size of the solution, the seconds to the
solution, and the number of programs listed before it.

With no arguments, it runs three small Hoogle+ queries with 30 seconds and a
heap of 2 GB each, so that @cabal bench@ stays short.

> hectare [hplus | stackoverflow | all | smoke] [seconds] [heap]
> hectare --query NAME [seconds]
> hectare --profile NAME SIZE
> hectare --generator NAME SIZE [DEPTH]
-}
module Main (main) where

import Control.Exception (evaluate)
import Data.List (elemIndex, find, nub, sort)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)
import System.Environment (getArgs, getExecutablePath)
import System.Exit (ExitCode (..))
import System.IO (hFlush, stdout)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import qualified Test.QuickCheck as QC
import Text.Printf (printf)

import Data.CFTA.Equality (edgeCount, nodeCount, reducePartially, refold, withoutRedundantEdges)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Synthesis
import Data.CFTA.Gen.Synthesis.HooglePlus
import Data.CFTA.Index (Depth (..), everyRank)

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["--query", name, seconds] -> runQuery name (read seconds)
        ["--profile", name, size] -> profileQuery name (read size)
        ["--generator", name, size] -> generatorQuery name (read size) Nothing
        ["--generator", name, size, depth] -> generatorQuery name (read size) (Just (read depth))
        [] -> runSuite "smoke" 30 "2G"
        [suite] -> runSuite suite 60 "8G"
        [suite, seconds] -> runSuite suite (read seconds) "8G"
        [suite, seconds, heap] -> runSuite suite (read seconds) heap
        _ -> fail "usage: hectare [hplus | stackoverflow | all] [seconds] [heap]"

-- | The queries of a suite with their library.
suiteQueries :: String -> [(Benchmark, Library)]
suiteQueries suite = case suite of
    "hplus" -> hplus
    "stackoverflow" -> stackOverflow
    "all" -> hplus <> stackOverflow
    "smoke" -> [query | query@(benchmark, _) <- hplus, benchmarkName benchmark `elem` ["map", "firstMatch", "headRest"]]
    _ -> []
  where
    hplus = [(benchmark, hooglePlus) | benchmark <- hooglePlusBenchmarks]
    stackOverflow = [(benchmark, hooglePlusWithAugmented) | benchmark <- stackOverflowBenchmarks]

-- | Run each query of a suite in a child process and print one row for each.
runSuite :: String -> Int -> String -> IO ()
runSuite suite seconds heap = do
    executable <- getExecutablePath
    putStrLn "query,outcome,size,seconds,listed"
    mapM_ (runChild executable) (suiteQueries suite)
  where
    runChild executable (benchmark, _) = do
        let name = Text.unpack $ benchmarkName benchmark
        (code, output, _) <-
            readProcessWithExitCode
                executable
                ["--query", name, show seconds, "+RTS", "-M" <> heap, "-RTS"]
                ""
        putStrLn $ case (code, lines output) of
            (ExitSuccess, row : _) -> row
            _ -> name <> ",crash,,,"
        hFlush stdout

-- | Search one query size by size, and print its row.
runQuery :: String -> Int -> IO ()
runQuery name seconds = case find ((== Text.pack name) . benchmarkName . fst) (suiteQueries "all") of
    Nothing -> fail $ "no query " <> name
    Just (benchmark, lib) -> do
        start <- getMonotonicTime
        found <- timeout (seconds * 1000000) $ search benchmark lib
        end <- getMonotonicTime
        putStrLn $ case found of
            Nothing -> name <> ",timeout,,,"
            Just Nothing -> printf "%s,unsolved,,%.3f," name (end - start)
            Just (Just (size, listed, at)) -> printf "%s,solved,%d,%.3f,%d" name size (at - start) listed

{- | The size, the number of programs listed before, and the time at which
the expected solution appears.
-}
search :: Benchmark -> Library -> IO (Maybe (Int, Int, Double))
search benchmark lib = go 1 0
  where
    expected = representative lib <$> benchmarkSolution benchmark
    go size listed
        | size > benchmarkSize benchmark = pure Nothing
        | otherwise = do
            let programs = solutionsOfSize lib (benchmarkQuery benchmark) size
            case break ((== expected) . Just) programs of
                (before, _ : _) -> do
                    count <- evaluate (length before)
                    at <- getMonotonicTime
                    pure $ Just (size, listed + count, at)
                (before, []) -> do
                    count <- evaluate (length before)
                    go (size + 1) (listed + count)

{- | The seconds of each phase of one size of a query: building the automaton,
reducing it, refolding it, and listing its programs, with the node and edge
counts after each phase.
-}
profileQuery :: String -> Int -> IO ()
profileQuery name size = case find ((== Text.pack name) . benchmarkName . fst) (suiteQueries "all") of
    Nothing -> fail $ "no query " <> name
    Just (benchmark, lib) -> do
        t0 <- getMonotonicTime
        let raw = rawSearchSpace lib (benchmarkQuery benchmark) size
        rawNodes <- evaluate (nodeCount raw)
        t1 <- getMonotonicTime
        reduced <- rounds (0 :: Int) raw
        reducedNodes <- evaluate (nodeCount reduced)
        t2 <- getMonotonicTime
        let folded = refold reduced
        foldedNodes <- evaluate (nodeCount folded)
        t3 <- getMonotonicTime
        listed <- evaluate (length (programsIn folded))
        t4 <- getMonotonicTime
        printf
            "%s size %d: build %.3f s (%d nodes, %d edges), reduce %.3f s (%d nodes, %d edges), refold %.3f s (%d nodes), list %.3f s (%d programs)\n"
            name
            size
            (t1 - t0)
            rawNodes
            (edgeCount raw)
            (t2 - t1)
            reducedNodes
            (edgeCount reduced)
            (t3 - t2)
            foldedNodes
            (t4 - t3)
            listed
  where
    -- The rounds of 'reduceFully', each with its time and size.
    rounds count node = do
        start <- getMonotonicTime
        next <- evaluate (withoutRedundantEdges (reducePartially node))
        nodes <- evaluate (nodeCount next)
        end <- getMonotonicTime
        printf "round %d: %.3f s, %d nodes, %d edges\n" count (end - start) nodes (edgeCount next)
        hFlush stdout
        if next == node || count + 1 >= reductionRounds then pure next else rounds (count + 1) next

{- | The programs of one size of a query as a generator: the count, the rank
of the expected solution, a check that the ranks list the programs of the
enumeration, a round trip from each rank to its term and back, and uniform
samples. With a depth, the typed terms are bounded by it.
-}
generatorQuery :: String -> Int -> Maybe Int -> IO ()
generatorQuery name size depth = case find ((== Text.pack name) . benchmarkName . fst) (suiteQueries "all") of
    Nothing -> fail $ "no query " <> name
    Just (benchmark, lib) -> do
        let query = benchmarkQuery benchmark
            generator = maybe programsOfSize (programsOfSizeUpToDepth . Depth) depth lib query size
            expected = representative lib <$> benchmarkSolution benchmark
            enumerated = solutionsOfSize lib query size
        total <- either (fail . show) pure (Gen.cardinality generator)
        ranked <- either (fail . show) pure (Gen.values generator)
        let roundTrips = and [(Gen.termAt generator rank >>= Gen.rankOf generator) == Right rank | rank <- everyRank total]
        samples <- maybe (fail "no uniform sampler") (QC.generate . QC.vectorOf 5) (Gen.lowerUniform generator)
        printf
            "%s size %d: %s ranks, %d distinct programs, expected at rank %s\n"
            name
            size
            (show total)
            (length (nub ranked))
            (maybe "none" show (expected >>= (`elemIndex` ranked)))
        printf
            "ranks list the enumerated programs: %s; rank round trip: %s; samples are members: %s\n"
            (show (sort (nub ranked) == sort (nub enumerated)))
            (show roundTrips)
            (show (all (`elem` ranked) samples))
        mapM_ (putStrLn . ("sample: " <>) . renderProgram) samples
