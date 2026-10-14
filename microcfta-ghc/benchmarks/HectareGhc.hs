{-# LANGUAGE OverloadedStrings #-}

{- | The Hoogle+ queries of Hectare's evaluation, synthesized with
"Data.CFTA.GHC.Fits": Hectare proposes programs over a library read from
GHC's exports, and the walk inside GHC's typechecker checks them.

The queries have their class constraints restored: an argument
@tcarg0 :: \@\@hplusTC\@\@Eq a@ becomes the constraint @Eq a@, and the expected
solution loses its dictionary arguments. The library is a rung of a ladder:
the Prelude; then also "Data.List", "Data.Maybe", "Data.Either", and
"Data.Char"; then also "Data.Map", qualified as @Map@. There are no
dictionary components.

The parent runs each query in a child process with a heap limit and a time
limit, as Hectare's evaluation does. Each row gives the query, the rung, the
outcome (@solved@, @other@ when other programs fit but not the expected one,
@unsolved@, @timeout@, @oom@, or @crash@), the bound, the size of the first
fit and of the expected one, the programs that Hectare proposed, the solver
calls, the seconds, the peak memory in megabytes, whether GHC accepts the
first fit as a program of the signature, and the first fit.

With no arguments, it runs three queries with the Prelude, 30 seconds and a
heap of 2 GB each, so that @cabal bench@ stays short. The variable
@HECTARE_GHC_TOP_CORE@ pins child @k@ to that core minus @k@,
@HECTARE_GHC_LOGS@ names a directory for the children's output, and
@HECTARE_GHC_TRACE@ makes a child print each program that it checks to its
standard error, with the seconds and the size.

> hectare-ghc [RUNG [SECONDS [HEAP [JOBS [NAME...]]]]]
> hectare-ghc --query NAME RUNG SECONDS
-}
module Main (main) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (modifyMVar, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Exception (AsyncException (HeapOverflow), try)
import Control.Monad (forM_, replicateM_, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isAlphaNum, isUpper)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (intercalate, isPrefixOf, partition)
import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)
import GHC.Stats (getRTSStats, getRTSStatsEnabled, max_mem_in_use_bytes)
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs, getExecutablePath, lookupEnv)
import System.Exit (ExitCode (..))
import System.IO (hFlush, hPutStrLn, stderr, stdout)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Text.Printf (printf)

import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.Internal.Check (Counters (..))
import Data.CFTA.GHC.Session
import Data.CFTA.Gen.Synthesis (Program (..), Query (..), Type (..), renderProgram, renderType)
import Data.CFTA.Gen.Synthesis.HooglePlus (Benchmark (..), hooglePlusBenchmarks)

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["--query", name, rung, seconds] -> runQuery name rung (read seconds)
        [] -> runSuite "prelude" 30 "2G" 2 ["map", "firstKey", "mergeEither"]
        rung : rest -> case rest of
            [] -> runSuite rung 120 "1400M" 1 []
            [seconds] -> runSuite rung (read seconds) "1400M" 1 []
            [seconds, heap] -> runSuite rung (read seconds) heap 1 []
            seconds : heap : jobs : names -> runSuite rung (read seconds) heap (read jobs) names

-- Queries

-- | A Hoogle+ query in GHC's terms.
data GhcQuery = GhcQuery
    { ghcName :: String
    , ghcConstraints :: [(String, Text)]
    -- ^ Each class constraint: the class and the type variable.
    , ghcArguments :: [(Text, Type)]
    , ghcGoal :: Type
    , ghcSolution :: Maybe Program
    -- ^ The expected solution with GHC's names and no dictionary arguments.
    , ghcSize :: Int
    -- ^ The size of the expected solution, or the benchmark size without the dictionaries.
    }

-- | A Hoogle+ benchmark with its class constraints restored.
fromBenchmark :: Benchmark -> GhcQuery
fromBenchmark benchmark =
    GhcQuery
        { ghcName = Text.unpack (benchmarkName benchmark)
        , ghcConstraints =
            [ (Text.unpack (Text.drop (Text.length dictionaryPrefix) name), variable)
            | (_, TCons name [TVar variable]) <- dictionaries
            ]
        , ghcArguments = plain
        , ghcGoal = queryGoal query
        , ghcSolution = solution
        , ghcSize = maybe (benchmarkSize benchmark - length dictionaries) programSize solution
        }
  where
    query = benchmarkQuery benchmark
    (dictionaries, plain) = partition dictionary (queryArguments query)
    dictionary (_, typ) = case typ of
        TCons name _ -> dictionaryPrefix `Text.isPrefixOf` name
        _ -> False
    solution = ghcProgram (map fst dictionaries) <$> benchmarkSolution benchmark

-- | The prefix of a Hoogle+ dictionary type.
dictionaryPrefix :: Text
dictionaryPrefix = "@@hplusTC@@"

-- | A Hoogle+ program with GHC's names and without the dictionary arguments.
ghcProgram :: [Text] -> Program -> Program
ghcProgram dictionaries = go
  where
    go program = case program of
        App function (Var name) | name `elem` dictionaries -> go function
        App function argument -> App (go function) (go argument)
        Var name -> Var (ghcName' name)
    ghcName' name = case name of
        "Pair" -> "(,)"
        "Cons" -> "(:)"
        "Nil" -> "[]"
        "$" -> "($)"
        _
            | Just inner <- Text.stripPrefix "(" name >>= Text.stripSuffix ")" -> "(" <> unqualified inner <> ")"
            | otherwise -> unqualified name
    unqualified name = case Text.span isAlphaNum name of
        (segment, rest)
            | Just after <- Text.stripPrefix "." rest
            , Just (first, _) <- Text.uncons segment
            , isUpper first
            , not (Text.null after) ->
                unqualified after
        _ -> name

-- | The number of components and arguments of a program.
programSize :: Program -> Int
programSize program = case program of
    Var _ -> 1
    App function argument -> programSize function + programSize argument

-- | The signature of a query: its class context, its arguments' types, and its goal.
signatureOf :: GhcQuery -> String
signatureOf query = context <> renderType (foldr (TFun . snd) (ghcGoal query) (ghcArguments query))
  where
    context = case ghcConstraints query of
        [] -> ""
        constraints -> "(" <> intercalate ", " [className <> " " <> Text.unpack variable | (className, variable) <- constraints] <> ") => "

{- | Hectare's pruning rule of the Hoogle+ library, with GHC's names: a list
function is not applied to @[]@.
-}
hooglePlusAvoid :: [([Text], Maybe [Text])]
hooglePlusAvoid =
    [
        (
            [ "listToMaybe"
            , "lefts"
            , "rights"
            , "partitionEithers"
            , "catMaybes"
            , "head"
            , "last"
            , "tail"
            , "init"
            , "null"
            , "length"
            , "reverse"
            , "concat"
            , "concatMap"
            , "sum"
            , "product"
            , "maximum"
            , "minimum"
            , "(!!)"
            , "(++)"
            ]
        , Just ["[]"]
        )
    ]

-- Libraries

-- | A rung of the library ladder: its name and its modules.
data Rung = Rung
    { rungName :: String
    , rungModules :: [Import]
    }

-- | The library ladder.
ladder :: [Rung]
ladder = [prelude, base, withMap]
  where
    prelude = Rung "prelude" [Import "Prelude" Nothing]
    base =
        Rung
            "base"
            (rungModules prelude <> [Import name Nothing | name <- ["Data.List", "Data.Maybe", "Data.Either", "Data.Char"]])
    withMap = Rung "map" (rungModules base <> [Import "Data.Map" (Just "Map")])

-- | The import declarations of a rung.
importLines :: Rung -> [String]
importLines rung = map line (rungModules rung)
  where
    line (Import name Nothing) = "import " <> name
    line (Import name (Just qualifier)) = "import qualified " <> name <> " as " <> qualifier

-- Runs

{- | Synthesize one query with a rung, size by size up to the size of the
expected solution, and print a row for each size and a result row. The
search stops at the expected solution.
-}
runQuery :: String -> String -> Int -> IO ()
runQuery name rungName' seconds = case [query | query <- map fromBenchmark hooglePlusBenchmarks, ghcName query == name] of
    [] -> fail ("no query " <> name)
    query : _ -> case [rung | rung <- ladder, rungName rung == rungName'] of
        [] -> fail ("no rung " <> rungName')
        rung : _ -> do
            start <- getMonotonicTime
            firstFit <- newIORef Nothing
            solved <- newIORef Nothing
            tracing <- isJust <$> lookupEnv "HECTARE_GHC_TRACE"
            outcome <- try . timeout (seconds * 1000000) $ withSession (importLines rung) $ \session -> do
                candidates <- candidatesOf session (rungModules rung)
                printf "candidates,%d\n" (length candidates)
                hFlush stdout
                signature <- typeOfExpression session ("undefined :: " <> signatureOf query)
                let options =
                        defaultOptions
                            { optionMaximumSize = ghcSize query
                            , optionAvoid = hooglePlusAvoid
                            , optionReport = Just report
                            , optionTrace = if tracing then Just trace else Nothing
                            }
                    trace size program = do
                        now <- getMonotonicTime
                        hPutStrLn stderr (printf "%.3f %d %s" (now - start) size (renderProgram program))
                    report size statistics = do
                        now <- getMonotonicTime
                        printf "size,%d,%s,%.3f\n" size (show statistics) (now - start)
                        hFlush stdout
                    accept fit = liftIO $ do
                        known <- readIORef firstFit
                        when (isNothing known) $ writeIORef firstFit (Just fit)
                        if Just (fitProgram fit) == ghcSolution query
                            then False <$ writeIORef solved (Just (fitSize fit))
                            else pure True
                statistics <- case signature of
                    Just typ -> fitsForSignature session options candidates typ (map fst (ghcArguments query)) accept
                    Nothing -> pure Nothing
                -- Check the first fit itself, as a program of the signature.
                found <- readIORef firstFit
                checked <- case found of
                    Just fit ->
                        accepts
                            session
                            ( "(\\"
                                <> unwords (map (Text.unpack . fst) (ghcArguments query))
                                <> " -> "
                                <> renderProgram (fitProgram fit)
                                <> ") :: "
                                <> signatureOf query
                            )
                    Nothing -> pure False
                pure (statistics, checked)
            end <- getMonotonicTime
            memory <- peakMemory
            found <- readIORef firstFit
            size <- readIORef solved
            let outcomeText :: String
                outcomeText = case outcome of
                    Left HeapOverflow -> "oom"
                    Left _ -> "crash"
                    Right Nothing -> "timeout"
                    Right (Just _) -> case (size, found) of
                        (Just _, _) -> "solved"
                        (Nothing, Just _) -> "other"
                        (Nothing, Nothing) -> "unsolved"
                programs, calls, checkedText :: String
                (programs, calls, checkedText) = case outcome of
                    Right (Just (Just statistics, checked)) ->
                        ( show (statisticsPrograms statistics)
                        , show (countSolverCalls (statisticsCounters statistics))
                        , if checked then "yes" else "no"
                        )
                    _ -> ("-", "-", "-")
            printf
                "result,%s,%s,%s,%d,%s,%s,%s,%s,%.3f,%d,%s,%s\n"
                name
                rungName'
                outcomeText
                (ghcSize query)
                (maybe "-" (show . fitSize) found)
                (maybe "-" show size)
                programs
                calls
                (end - start)
                memory
                checkedText
                (maybe "-" (renderProgram . fitProgram) found)

-- | The peak memory in use in megabytes, when the RTS keeps statistics.
peakMemory :: IO Int
peakMemory = do
    enabled <- getRTSStatsEnabled
    if enabled then (\stats -> fromIntegral (max_mem_in_use_bytes stats `div` (1024 * 1024))) <$> getRTSStats else pure 0

{- | Run each query in a child process with a heap limit and a time limit,
several at a time, and print the result row of each. With no names, the
suite is the 45 Hoogle+ queries.
-}
runSuite :: String -> Int -> String -> Int -> [String] -> IO ()
runSuite rung seconds heap jobs names = do
    executable <- getExecutablePath
    top <- fmap read <$> lookupEnv "HECTARE_GHC_TOP_CORE"
    logs <- lookupEnv "HECTARE_GHC_LOGS"
    forM_ logs $ \directory -> createDirectoryIfMissing True (directory <> "/" <> rung)
    let queries = if null names then map (ghcName . fromBenchmark) hooglePlusBenchmarks else names
    queue <- newMVar queries
    output <- newMVar ()
    done <- newEmptyMVar
    putStrLn "result,query,rung,outcome,bound,first,solved,programs,calls,seconds,memory,checked,program"
    hFlush stdout
    forM_ [0 .. jobs - 1] $ \worker -> forkIO $ do
        let loop = do
                next <- modifyMVar queue $ \pending -> pure $ case pending of
                    [] -> ([], Nothing)
                    query : rest -> (rest, Just query)
                case next of
                    Nothing -> putMVar done ()
                    Just query -> do
                        let child =
                                ["--kill-after=10", show (seconds + 60), executable, "--query", query, rung, show seconds]
                                    <> ["+RTS", "-M" <> heap, "-T", "-RTS"]
                            (command, commandArguments) = case top of
                                Just core -> ("taskset", ["-c", show (core - worker :: Int), "timeout"] <> child)
                                Nothing -> ("timeout", child)
                        (code, out, err) <- readProcessWithExitCode command commandArguments ""
                        forM_ logs $ \directory ->
                            writeFile (directory <> "/" <> rung <> "/" <> query <> ".log") (out <> err <> "exit " <> show code <> "\n")
                        let row = case (code, [line | line <- lines out, "result," `isPrefixOf` line]) of
                                (_, line : _) -> line
                                (ExitFailure 124, []) -> "result," <> query <> "," <> rung <> ",timeout,,,,,,,,,"
                                (ExitFailure 251, []) -> "result," <> query <> "," <> rung <> ",oom,,,,,,,,,"
                                _ -> "result," <> query <> "," <> rung <> ",crash,,,,,,,,,"
                        withMVar output $ \() -> putStrLn row >> hFlush stdout
                        loop
        loop
    replicateM_ jobs (takeMVar done)
