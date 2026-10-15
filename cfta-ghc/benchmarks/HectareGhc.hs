{-# LANGUAGE OverloadedStrings #-}

{- | The Hoogle+ queries of Hectare's evaluation, synthesized with
"Data.CFTA.GHC.Fits": Hectare proposes programs over a library read from
GHC's exports, and the walk inside GHC's typechecker checks them.

The queries have their class constraints restored: an argument
@tcarg0 :: \@\@hplusTC\@\@Eq a@ becomes the constraint @Eq a@, and the expected
solution loses its dictionary arguments. The library is a rung of a ladder:
the Prelude; then also "Data.List", "Data.Maybe", "Data.Either", and
"Data.Char"; then also "Data.Map", qualified as @Map@. There are no
dictionary components. The Stack Overflow queries have their own rung,
@so@: the second rung and "Data.Function", for the components that Hectare
adds for them.

The parent runs each query in a child process with a heap limit and a time
limit, as Hectare's evaluation does. Each row gives the query, the rung, the
outcome (@solved@, @other@ when other programs fit but not the expected one,
@unsolved@, @timeout@, @oom@, or @crash@), the bound, the size of the first
fit and of the expected one, the rank of the expected one among the fits
and among the fits that use every part of themselves ('comesLast'),
the programs that Hectare proposed, the solver
calls, the seconds, the seconds of Hectare's construction, reduction, and
listing, of the checks in the typechecker, and of the solver calls in the
checks, the peak memory and the allocation in megabytes, the fits skipped
for the normal form of an earlier fit, the seconds of the normal forms,
whether GHC accepts the first fit as a program of the signature, the typed
terms that Hectare listed, the fits and the fits that use every part of
themselves, and the first fit. With normal forms, a fit with the normal
form of the expected solution counts as the solution. The walk itself stops
at the time limit, so that a row of a timeout has its figures too. The
search is the one of the tools, with 'optionFits' at its default.

With no arguments, it runs three queries with the Prelude, 30 seconds and a
heap of 2 GB each, so that @cabal bench@ stays short. The variable
@HECTARE_GHC_TOP_CORE@ pins child @k@ to that core minus @k@,
@HECTARE_GHC_LOGS@ names a directory for the children's output, and
@HECTARE_GHC_TRACE@ makes a child print each program that it checks to its
standard error, with the seconds and the size, and @HECTARE_GHC_NORMAL_FORMS=off@
turns off the normal forms of the fits ('optionNormalForms'). The children
search with Hectare's curried types; @HECTARE_GHC_FIRST_ORDER@ makes them
search with its first-order types ('optionCurried'), and
@HECTARE_GHC_DEFAULTED@ with only the default of a type variable that a
program does not determine ('optionOnlyDefaulted').
@HECTARE_GHC_TYPE_DOMAINS@ gives a type variable of kind @Type@ the domain
of its classes ('optionTypeDomains'). The names @hplus@ and
@stackoverflow@ stand for the queries of each suite; the Stack Overflow
queries are the queries of Hectare's evaluation, with GHC's library of the
rung. Next to the Hoogle+ queries, the parent takes the names of the
differential queries ('differential'), where the erasure loses information.

The variable @HECTARE_GHC_MODE@ gives the mode ('optionMode'): @hectare@
(mode (a), the default) or @states@ (mode (b), "Data.CFTA.GHC.States").
With mode (b), a child also prints a row @figures@ with the figures of the
states, and the parent prints it after the result row.

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
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (intercalate, isPrefixOf, partition)
import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)
import GHC.Stats (allocated_bytes, getRTSStats, getRTSStatsEnabled, max_mem_in_use_bytes)
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
import Data.CFTA.Gen.Synthesis (Program (..), Query (..), Type (..), parseProgram, renderProgram, renderType)
import Data.CFTA.Gen.Synthesis.HooglePlus (Benchmark (..), hooglePlusBenchmarks, stackOverflowBenchmarks)

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
    , ghcSignature :: String
    -- ^ The query's signature, in Haskell's syntax.
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
    signed
        GhcQuery
            { ghcName = Text.unpack (benchmarkName benchmark)
            , ghcSignature = ""
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
    signed ghcQuery = ghcQuery{ghcSignature = signatureOf ghcQuery}
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
            -- Hoogle+'s (/=) with an Ord dictionary is GHC's (/=).
            | Just plain <- Text.stripSuffix "_Ord" name -> ghcName' plain
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

{- | Queries where the erasure loses information: components that are
polymorphic over a type constructor (Functor, Applicative, Monad, Foldable,
Traversable) at Maybe, Either e, pairs, lists, or a rigid variable of the
signature, or at an intermediate type that no head of the signature has, as
the Maybe in @length (lookup k xs)@, or at the default of GHC's
@ExtendedDefaultRules@, as the list in @length (pure x)@. Each has its
signature, its argument names, and its expected program; the arguments'
Hectare types are not used.
-}
differential :: [GhcQuery]
differential =
    [ query "hkJoin" "Monad m => m (m a) -> m a" ["x"] "(>>=) x id"
    , query "hkFmapFst" "Functor f => f (a, b) -> f a" ["x"] "fmap fst x"
    , query "hkJoinMaybe" "Maybe (Maybe a) -> Maybe a" ["x"] "(>>=) x id"
    , query "hkBind" "Monad m => (a -> m b) -> m a -> m b" ["f", "x"] "(>>=) x f"
    , query "hkPureSingleton" "Applicative f => a -> f [a]" ["x"] "pure ((:) x [])"
    , query "addPairPlus" "Num a => (a, a) -> a" ["p"] "(+) (fst p) (snd p)"
    , query "mapFunctor" "(a -> b) -> Maybe a -> Maybe b" ["f", "m"] "fmap f m"
    , query "maybeBind" "Maybe a -> (a -> Maybe b) -> Maybe b" ["m", "f"] "(>>=) m f"
    , query "eitherBind" "Either e a -> (a -> Either e b) -> Either e b" ["x", "f"] "(>>=) x f"
    , query "sequenceMaybes" "[Maybe a] -> Maybe [a]" ["xs"] "sequence xs"
    , query "traverseMaybe" "(a -> Maybe b) -> [a] -> Maybe [b]" ["f", "xs"] "traverse f xs"
    , query "traverseEither" "(a -> Either e b) -> [a] -> Either e [b]" ["f", "xs"] "traverse f xs"
    , query "mapSecond" "(b -> c) -> (a, b) -> (a, c)" ["f", "p"] "fmap f p"
    , query "mapEitherList" "(a -> b) -> Either e [a] -> Either e [b]" ["f", "e"] "fmap (map f) e"
    , query "liftPair" "Applicative f => f a -> f b -> f (a, b)" ["x", "y"] "liftA2 (,) x y"
    , query "kleisli" "Monad m => (a -> m b) -> (b -> m c) -> a -> m c" ["f", "g", "x"] "(>>=) (f x) g"
    , query "foldableSum" "Foldable t => t Int -> Int" ["xs"] "sum xs"
    , query "foldableToList" "Foldable t => t a -> [a]" ["xs"] "foldr (:) [] xs"
    , query "traversableSequence" "Traversable t => t (Maybe a) -> Maybe (t a)" ["xs"] "sequenceA xs"
    , query "concatMaybe" "Maybe [a] -> [a]" ["m"] "concat m"
    , query "sumMaybe" "Maybe Int -> Int" ["m"] "sum m"
    , query "lengthPair" "(a, b) -> Int" ["p"] "length p"
    , -- The gap test: a Foldable or Traversable at an intermediate Maybe, of
      -- lookup and find (rungs 1 and 2), listToMaybe (rung 2), or Map.lookup
      -- (rung 3).
      query "gapLengthLookup" "Eq k => k -> [(k, v)] -> Int" ["k", "xs"] "length (lookup k xs)"
    , query "gapNullLookup" "Eq k => k -> [(k, v)] -> Bool" ["k", "xs"] "null (lookup k xs)"
    , query "gapSumLookup" "Eq k => k -> [(k, Int)] -> Int" ["k", "xs"] "sum (lookup k xs)"
    , query "gapConcatLookup" "Eq k => k -> [(k, [a])] -> [a]" ["k", "xs"] "concat (lookup k xs)"
    , query "gapAndLookup" "Eq k => k -> [(k, Bool)] -> Bool" ["k", "xs"] "and (lookup k xs)"
    , query "gapMaximumLookup" "(Eq k, Ord v) => k -> [(k, v)] -> v" ["k", "xs"] "maximum (lookup k xs)"
    , query "gapElemLookup" "(Eq k, Eq v) => v -> k -> [(k, v)] -> Bool" ["v", "k", "xs"] "elem v (lookup k xs)"
    , query "gapSequenceLookup" "Eq k => k -> [(k, [a])] -> [Maybe a]" ["k", "xs"] "sequenceA (lookup k xs)"
    , query "gapTraverseLookup" "Eq k => (v -> [b]) -> k -> [(k, v)] -> [Maybe b]" ["f", "k", "xs"] "traverse f (lookup k xs)"
    , query "gapToListLookup" "Eq k => k -> [(k, v)] -> [v]" ["k", "xs"] "foldr (:) [] (lookup k xs)"
    , query "gapLengthFind" "(a -> Bool) -> [a] -> Int" ["p", "xs"] "length (find p xs)"
    , query "gapNullFind" "(a -> Bool) -> [a] -> Bool" ["p", "xs"] "null (find p xs)"
    , query "gapSumListToMaybe" "[Int] -> Int" ["xs"] "sum (listToMaybe xs)"
    , query "gapLengthMapLookup" "Ord k => k -> Map.Map k [a] -> Int" ["k", "m"] "length (Map.lookup k m)"
    , -- A Functor between them: listToMaybe fixes the variable of fmap, and
      -- fmap fixes the variable of null (rung 2).
      query "gapNullFmapListToMaybe" "(a -> b) -> [a] -> Bool" ["f", "xs"] "null (fmap f (listToMaybe xs))"
    , -- Programs that only a default types: no part fixes the variable of
      -- kind * -> *, and GHC's ExtendedDefaultRules give it the list type
      -- (rung 1).
      query "defaultLengthPure" "a -> Int" ["x"] "length (pure x)"
    , query "defaultNullPure" "a -> Bool" ["x"] "null (pure x)"
    ]
  where
    query name signature arguments expected =
        let solution = either error id (parseProgram expected)
         in GhcQuery
                { ghcName = name
                , ghcSignature = signature
                , ghcConstraints = []
                , ghcArguments = [(argument, TVar "unused") | argument <- arguments]
                , ghcGoal = TVar "unused"
                , ghcSolution = Just solution
                , ghcSize = programSize solution
                }

-- | Every query: the Hoogle+ ones, the Stack Overflow ones, then the differential ones.
allQueries :: [GhcQuery]
allQueries = map fromBenchmark (hooglePlusBenchmarks <> stackOverflowBenchmarks) <> differential

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

-- Libraries

-- | A rung of the library ladder: its name and its modules.
data Rung = Rung
    { rungName :: String
    , rungModules :: [Import]
    }

-- | The library ladder.
ladder :: [Rung]
ladder = [prelude, base, withMap, stackOverflow]
  where
    prelude = Rung "prelude" [Import "Prelude" Nothing]
    base =
        Rung
            "base"
            (rungModules prelude <> [Import name Nothing | name <- ["Data.List", "Data.Maybe", "Data.Either", "Data.Char"]])
    withMap = Rung "map" (rungModules base <> [Import "Data.Map" (Just "Map")])
    stackOverflow = Rung "so" (rungModules base <> [Import "Data.Function" Nothing])

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
runQuery name rungName' seconds = case [query | query <- allQueries, ghcName query == name] of
    [] -> fail ("no query " <> name)
    query : _ -> case [rung | rung <- ladder, rungName rung == rungName'] of
        [] -> fail ("no rung " <> rungName')
        rung : _ -> do
            start <- getMonotonicTime
            firstFit <- newIORef Nothing
            solved <- newIORef Nothing
            -- The fits so far, and those that use every part of themselves.
            counts <- newIORef (0 :: Int, 0 :: Int)
            tracing <- isJust <$> lookupEnv "HECTARE_GHC_TRACE"
            firstOrder <- isJust <$> lookupEnv "HECTARE_GHC_FIRST_ORDER"
            defaulted <- isJust <$> lookupEnv "HECTARE_GHC_DEFAULTED"
            typeDomains <- isJust <$> lookupEnv "HECTARE_GHC_TYPE_DOMAINS"
            normalForms <- (/= Just "off") <$> lookupEnv "HECTARE_GHC_NORMAL_FORMS"
            -- The normal forms of programs, built at the first fit.
            normalRef <- newIORef Nothing
            mode <- maybe (pure (optionMode defaultOptions)) (either fail pure . readMode) =<< lookupEnv "HECTARE_GHC_MODE"
            -- The walk stops at the time limit; this limit is for the rest.
            outcome <- try . timeout ((seconds + 30) * 1000000) $ withSession (importLines rung) $ \session -> do
                candidates <- candidatesOf session (rungModules rung)
                printf "candidates,%d\n" (length candidates)
                hFlush stdout
                signature <- typeOfExpression session ("undefined :: " <> ghcSignature query)
                ready <- getMonotonicTime
                let options =
                        defaultOptions
                            { optionMaximumSize = ghcSize query
                            , optionSeconds = Just (fromIntegral seconds - (ready - start))
                            , optionAvoid = hectareAvoid
                            , optionMode = mode
                            , optionReport = Just report
                            , optionTrace = if tracing then Just trace else Nothing
                            , optionCurried = not firstOrder
                            , optionOnlyDefaulted = defaulted
                            , optionTypeDomains = typeDomains
                            , optionNormalForms = normalForms
                            }
                    -- With normal forms, a fit with the normal form of the solution is the solution.
                    isSolution normal program
                        | normalForms =
                            maybe False (\solution -> isJust (normal solution) && normal program == normal solution) (ghcSolution query)
                        | otherwise = Just program == ghcSolution query
                    trace size program = do
                        now <- getMonotonicTime
                        hPutStrLn stderr (printf "%.3f %d %s" (now - start) size (renderProgram program))
                    report size statistics = do
                        now <- getMonotonicTime
                        printf "size,%d,%s,%.3f\n" size (show statistics) (now - start)
                        hFlush stdout
                    accept fit = do
                        normal <-
                            if normalForms
                                then do
                                    built <- liftIO (readIORef normalRef)
                                    case built of
                                        Just cached -> pure cached
                                        Nothing -> do
                                            fresh <- normalFormsOf candidates
                                            liftIO (writeIORef normalRef (Just fresh))
                                            pure fresh
                                else pure (const Nothing)
                        liftIO $ do
                            known <- readIORef firstFit
                            when (isNothing known) $ writeIORef firstFit (Just fit)
                            modifyIORef' counts (\(all', using) -> (all' + 1, if comesLast fit then using else using + 1))
                            if isSolution normal (fitProgram fit)
                                then False <$ writeIORef solved (Just (fitSize fit))
                                else pure True
                statistics <- case signature of
                    Just typ -> fitsForSignature session options candidates typ (map fst (ghcArguments query)) accept
                    Nothing -> pure Nothing
                forM_ (statisticsStates =<< statistics) $ \figures -> printf "figures,%s,%s\n" name (show figures) >> hFlush stdout
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
                                <> ghcSignature query
                            )
                    Nothing -> pure False
                pure (statistics, checked)
            end <- getMonotonicTime
            (memory, allocated) <- memoryOf
            found <- readIORef firstFit
            size <- readIORef solved
            (rank, rankUsing) <- readIORef counts
            let outcomeText :: String
                outcomeText = case outcome of
                    Left HeapOverflow -> "oom"
                    Left _ -> "crash"
                    Right Nothing -> "timeout"
                    Right (Just (statistics, _)) -> case (size, found) of
                        (Just _, _) -> "solved"
                        _ | maybe False statisticsOutOfTime statistics -> "timeout"
                        (Nothing, Just _) -> "other"
                        (Nothing, Nothing) -> "unsolved"
                programs, calls, parts, mergedText, checkedText, runs :: String
                (programs, calls, parts, mergedText, checkedText, runs) = case outcome of
                    Right (Just (Just statistics, checked)) ->
                        ( show (statisticsPrograms statistics)
                        , show (countSolverCalls (statisticsCounters statistics))
                        , intercalate
                            ","
                            [ printf "%.3f" (fromIntegral (part statistics) / 1e9 :: Double)
                            | part <-
                                [ statisticsBuildNanos
                                , statisticsReduceNanos
                                , statisticsListNanos
                                , statisticsCheckNanos
                                , countSolverNanos . statisticsCounters
                                ]
                            ]
                        , printf "%d,%.4f" (statisticsMerged statistics) (fromIntegral (statisticsNormalNanos statistics) / 1e9 :: Double)
                        , if checked then "yes" else "no"
                        , show (statisticsRuns statistics)
                        )
                    _ -> ("-", "-", "-,-,-,-,-", "-,-", "-", "-")
            printf
                "result,%s,%s,%s,%d,%s,%s,%s,%s,%s,%s,%.3f,%s,%d,%d,%s,%s,%s,%d,%d,%s\n"
                name
                rungName'
                outcomeText
                (ghcSize query)
                (maybe "-" (show . fitSize) found)
                (maybe "-" show size)
                (if isJust size then show rank else "-")
                (if isJust size then show rankUsing else "-")
                programs
                calls
                (end - start)
                parts
                memory
                allocated
                mergedText
                checkedText
                runs
                rank
                rankUsing
                (maybe "-" (renderProgram . fitProgram) found)

-- | Read a mode: @hectare@ or @states@.
readMode :: String -> Either String Mode
readMode text = case text of
    "hectare" -> Right Hectare
    "states" -> Right States
    _ -> Left ("no mode " <> text)

-- | The peak memory in use and the bytes allocated, in megabytes, when the RTS keeps statistics.
memoryOf :: IO (Int, Int)
memoryOf = do
    enabled <- getRTSStatsEnabled
    if enabled
        then (\stats -> (megabytes (max_mem_in_use_bytes stats), megabytes (allocated_bytes stats))) <$> getRTSStats
        else pure (0, 0)
  where
    megabytes bytes = fromIntegral (bytes `div` (1024 * 1024))

{- | Run each query in a child process with a heap limit and a time limit,
several at a time, and print the result row of each. With no names, the
suite is the 45 Hoogle+ queries, or the 19 Stack Overflow queries on the
rung @so@, and the name @stackoverflow@ stands for the 19 Stack Overflow
queries.
-}
runSuite :: String -> Int -> String -> Int -> [String] -> IO ()
runSuite rung seconds heap jobs names = do
    executable <- getExecutablePath
    top <- fmap read <$> lookupEnv "HECTARE_GHC_TOP_CORE"
    logs <- lookupEnv "HECTARE_GHC_LOGS"
    forM_ logs $ \directory -> createDirectoryIfMissing True (directory <> "/" <> rung)
    let suite benchmarks = map (ghcName . fromBenchmark) benchmarks
        queries = case names of
            [] -> suite (if rung == "so" then stackOverflowBenchmarks else hooglePlusBenchmarks)
            ["hplus"] -> suite hooglePlusBenchmarks
            ["stackoverflow"] -> suite stackOverflowBenchmarks
            _ -> names
    queue <- newMVar queries
    output <- newMVar ()
    done <- newEmptyMVar
    putStrLn
        "result,query,rung,outcome,bound,first,solved,rank,using,programs,calls,seconds,build,reduce,list,check,solver,memory,allocated,merged,normal,checked,runs,fits,usingfits,program"
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
                                (ExitFailure 124, []) -> "result," <> query <> "," <> rung <> ",timeout,,,,,,,,,,,,,,,,,,,,,,"
                                (ExitFailure 251, []) -> "result," <> query <> "," <> rung <> ",oom,,,,,,,,,,,,,,,,,,,,,,"
                                _ -> "result," <> query <> "," <> rung <> ",crash,,,,,,,,,,,,,,,,,,,,,,"
                        let extra = [line | line <- lines out, "figures," `isPrefixOf` line]
                        withMVar output $ \() -> mapM_ putStrLn (row : extra) >> hFlush stdout
                        loop
        loop
    replicateM_ jobs (takeMVar done)
