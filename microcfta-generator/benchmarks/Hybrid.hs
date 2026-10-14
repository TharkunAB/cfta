{-# LANGUAGE OverloadedStrings #-}

{- | Hegel and the hybrid of "Data.CFTA.Gen.Synthesis.Hybrid" on the same
refinement-typed queries.

The @hegel@ suite has the queries of the @hegel@ benchmark without
conditionals, each with its own small library. The @large@ suite has a
large polymorphic library: the Hoogle+ components of the @hectare@
benchmark (without @($)@) and the 20 refined list and pair components of
Hegel's queries. Its queries are three Hoogle+ queries with a refined goal,
and Nth_Incr1 and RevApp1.

The parent runs each query in a child process with a heap limit and a time
limit, first with Hegel and then with the hybrid. The hybrid has 30 seconds,
and then Hegel runs on the query; @hybrid-only@ has no fallback. Each row of
the CSV gives the library, the query, the tool, the outcome (@solved@,
@fallback@ when Hegel solved it after the hybrid's 30 seconds, @unsolved@,
@timeout@, or @crash@), the applications of the solution, the seconds, the
entailment queries, the undecided queries, and the solution.

With no arguments, it runs three small queries with 60 seconds and a heap of
2 GB each, so that @cabal bench@ stays short.

> hybrid [hegel | large | all] [seconds] [heap]
> hybrid --query [hegel | hybrid | hybrid-only | abstracting] [hegel | large] NAME seconds
-}
module Main (main) where

import Data.List (find)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)
import System.Environment (getArgs, getExecutablePath)
import System.Exit (ExitCode (..))
import System.IO (hFlush, stdout)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Text.Printf (printf)

import Data.CFTA.Formula (Name (..), Sort (..))
import Data.CFTA.Gen.Synthesis (Program (..), Type (..), renderProgram)
import Data.CFTA.Gen.Synthesis.HegelBenchmarks
import Data.CFTA.Gen.Synthesis.HooglePlus (hooglePlusComponents)
import Data.CFTA.Gen.Synthesis.Hybrid
import Data.CFTA.Gen.Synthesis.Liquid
import Data.CFTA.Refinement (Entailment)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Timeout)

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["--query", tool, suite, name, seconds] -> runQuery tool suite name (read seconds)
        [] -> runSuite smoke 60 "2G"
        [suite] -> runSuite (suiteQueries suite) 180 "8G"
        [suite, seconds] -> runSuite (suiteQueries suite) (read seconds) "8G"
        [suite, seconds, heap] -> runSuite (suiteQueries suite) (read seconds) heap
        _ -> fail "usage: hybrid [hegel | large | all] [seconds] [heap]"

-- | A query of a suite: the components, the query, and Hegel's bound on its size.
data Entry = Entry [Component] LiquidQuery Int

-- | The queries of a suite, as the library and the name.
suiteQueries :: String -> [(String, String)]
suiteQueries suite = case suite of
    "hegel" -> hegelQueries
    "large" -> largeQueries
    "all" -> hegelQueries <> largeQueries
    _ -> []
  where
    hegelQueries = [("hegel", Text.unpack (liquidName benchmark)) | benchmark <- liquidBenchmarks, not (liquidConditionals benchmark)]
    largeQueries = [("large", Text.unpack name) | (name, _) <- largeLibraryQueries]

-- | Three small queries of the @hegel@ suite.
smoke :: [(String, String)]
smoke = [("hegel", name) | name <- ["RevApp1", "Nth_Incr1", "MapDouble1"]]

-- | The query of a suite with a name.
findEntry :: String -> String -> Maybe Entry
findEntry suite name = case suite of
    "hegel" -> do
        benchmark <- find ((== Text.pack name) . liquidName) liquidBenchmarks
        pure $ Entry (liquidLibrary benchmark) (liquidQuery benchmark) (liquidBound benchmark)
    "large" -> (\query -> Entry largeComponents query 5) <$> lookup (Text.pack name) largeLibraryQueries
    _ -> Nothing

-- | Run each query in a child process, with Hegel and then with the hybrid, and print one row for each.
runSuite :: [(String, String)] -> Int -> String -> IO ()
runSuite queries seconds heap = do
    executable <- getExecutablePath
    putStrLn "library,query,tool,outcome,applications,seconds,queries,undecided,solution"
    mapM_ (runChild executable) [(suite, name, tool) | (suite, name) <- queries, tool <- ["hegel", "hybrid"]]
  where
    runChild executable (suite, name, tool) = do
        (code, output, _) <-
            readProcessWithExitCode
                executable
                ["--query", tool, suite, name, show seconds, "+RTS", "-M" <> heap, "-RTS"]
                ""
        putStrLn $ case (code, lines output) of
            (ExitSuccess, row : _) -> row
            _ -> suite <> "," <> name <> "," <> tool <> ",crash,,,,,"
        hFlush stdout

{- | The time limit of one solver query, in milliseconds, as in the @hegel@
benchmark.
-}
queryLimit :: Int
queryLimit = 100

-- | Synthesize one query with one tool and print its row.
runQuery :: String -> String -> String -> Int -> IO ()
runQuery tool suite name seconds = case findEntry suite name of
    Nothing -> fail $ "no query " <> name
    Just (Entry components query bound) ->
        withZ3Timeout
            queryLimit
            [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
            []
            $ \solver -> do
                start <- getMonotonicTime
                let hegelOptions = defaultOptions{optionMaximumSize = bound}
                    withFallback = defaultHybridOptions{hybridFallback = Just (fallbackSeconds, hegelOptions)}
                result <- timeout (seconds * 1000000) $ case tool of
                    "hegel" -> hegelRow solver hegelOptions components query
                    "hybrid" -> hybridRow solver withFallback components query
                    "hybrid-only" -> hybridRow solver defaultHybridOptions{hybridFallback = Nothing} components query
                    "abstracting" -> hybridRow solver withFallback{hybridPrecise = False} components query
                    _ -> fail $ "no tool " <> tool
                end <- getMonotonicTime
                putStrLn $ case result of
                    Nothing -> printf "%s,%s,%s,timeout,,,,," suite name tool
                    Just (outcome, size, queries, undecided, solution) ->
                        printf
                            "%s,%s,%s,%s,%s,%.3f,%d,%d,%s"
                            suite
                            name
                            tool
                            outcome
                            size
                            (end - start)
                            queries
                            undecided
                            (show solution)

-- | A row's outcome, the applications of the solution, the queries, the undecided queries, and the solution.
type Row = (String, String, Int, Int, String)

{- | The seconds of the hybrid before Hegel runs, in the @hybrid@ and
@abstracting@ tools.
-}
fallbackSeconds :: Int
fallbackSeconds = 30

-- | Hegel on a query, with the reduction steps of the paper and a bound on the size.
hegelRow :: Entailment -> Options -> [Component] -> LiquidQuery -> IO Row
hegelRow solver options components query = hegelResult <$> synthesize solver options components query

-- | The row of a result of Hegel.
hegelResult :: Either String Outcome -> Row
hegelResult result = case result of
    Left err -> ("error", "", 0, 0, err)
    Right outcome ->
        let Statistics size _ _ queries undecided = outcomeStatistics outcome
         in case outcomeSolutions outcome of
                first : _ -> ("solved", show size, queries, undecided, renderTerm first)
                [] -> ("unsolved", "", queries, undecided, "")

{- | The hybrid on a query. A query that Hegel solves after the fallback has
the outcome @fallback@, and its queries are those of both.
-}
hybridRow :: Entailment -> HybridOptions -> [Component] -> LiquidQuery -> IO Row
hybridRow solver options components query = do
    outcome <- synthesizeHybrid solver options components query
    let HybridStatistics _ _ queries undecided = hybridStatistics outcome
    pure $ case (hybridSolution outcome, hybridFallbackOutcome outcome) of
        (Just program, _) -> ("solved", show (applications program), queries, undecided, renderProgram program)
        (Nothing, Just result) -> case hegelResult result of
            ("solved", size, hegelQueries, hegelUndecided, solution) ->
                ("fallback", size, queries + hegelQueries, undecided + hegelUndecided, solution)
            (other, size, hegelQueries, hegelUndecided, solution) ->
                (other, size, queries + hegelQueries, undecided + hegelUndecided, solution)
        (Nothing, Nothing) -> ("unsolved", "", queries, undecided, "")

-- | The applications of a program: each head applied to its arguments counts one.
applications :: Program -> Int
applications program = case spine program [] of
    [] -> 0
    arguments -> 1 + sum (map applications arguments)
  where
    spine (App function argument) rest = spine function (argument : rest)
    spine (Var _) rest = rest

-- The large library

{- | A refinement type without refinements: a parameter @p@ and its index for
each argument of a function type. A function parameter keeps its function
type as a base type.
-}
plainRType :: Type -> RType
plainRType = go (0 :: Int)
  where
    go index (TFun parameter result) = RArrow ("p" <> Text.pack (show index)) (plain parameter) (go (index + 1) result)
    go _ typ = plain typ

-- | The Hoogle+ components without @($)@ and without refinements, and the refined list and pair components.
largeComponents :: [Component]
largeComponents =
    [(name, plainRType typ) | (name, typ) <- hooglePlusComponents, name /= "(Data.Function.$)"]
        <> listLibrary
        <> pairLibrary

{- | Three Hoogle+ queries with one refinement in the goal and the
preconditions that it needs, and two of Hegel's queries.
-}
largeLibraryQueries :: [(Text, LiquidQuery)]
largeLibraryQueries =
    [ ("singletonList", query "x:a -> {v:[a] | len v = 1 && hd v = x}")
    ,
        ( "appendN"
        , query "n:{v:Int | v >= 0} -> xs:{v:[a] | len v >= 1 && n <= len v} -> {v:[a] | len v = n + len xs && lst v = lst xs}"
        )
    ,
        ( "takeNdropM"
        , query
            "n:{v:Int | v >= 0} -> m:{v:Int | v >= 0} -> xs:{v:[a] | n <= len v && m <= len v} -> {v:([a], [a]) | len (proj1 v) = n && len (proj2 v) = len xs - m}"
        )
    ]
        <> [ (liquidName benchmark, liquidQuery benchmark)
           | benchmark <- liquidBenchmarks
           , liquidName benchmark `elem` ["Nth_Incr1", "RevApp1"]
           ]
  where
    query = either error id . parseQuery
