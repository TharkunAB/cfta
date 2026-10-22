{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Specftacular (
    module Specftacular.Types,
    module Data.Proxy,
    ftacularSpec,
    discoverMonomorphic,
    experimentalPhases,
    SearchOptions (..),
    Diagnostics (..),
    defaultOptions,
    parseOptions,
    searchPhases,
) where

import qualified Data.Bifunctor as Bi
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import qualified Specftacular.CompiledPruning as Compile
import qualified Specftacular.DecisionTree as DT
import Specftacular.Pruning (prunedTerms)
import Specftacular.Rewriting
import Specftacular.Types
import Specftacular.Utils

import Control.Concurrent (
    forkIO,
    forkIOWithUnmask,
    forkOn,
    getNumCapabilities,
    killThread,
    myThreadId,
    threadDelay,
    throwTo,
 )
import Control.Concurrent.MVar (newEmptyMVar, putMVar, readMVar, takeMVar)
import Control.Exception (
    AllocationLimitExceeded (..),
    Exception (..),
    SomeException,
    asyncExceptionFromException,
    asyncExceptionToException,
    bracket,
    evaluate,
    finally,
    handleJust,
    mask,
    onException,
    throwIO,
    try,
    uninterruptibleMask_,
 )
import Control.Monad (foldM, unless, void, when)
import Data.CFTA.Equality (
    Edge (Edge),
    Node (Node),
    fixWithin,
    reducePartially,
    refold,
    union,
    withoutRedundantEdges,
 )
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Template (Template (..))
import Data.Char (isAlphaNum)
import Data.IORef (IORef, atomicModifyIORef', modifyIORef', newIORef, readIORef, writeIORef)
import Data.Int (Int64)
import Data.List hiding (union)
import Data.Maybe (fromMaybe, isJust, mapMaybe, maybeToList)
import qualified Data.Text as T
import Data.Unique (Unique, newUnique)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Conc (disableAllocationLimit, enableAllocationLimit, getAllocationCounter, setAllocationCounter)
import GHC.Stats (
    GCDetails (gcdetails_live_bytes),
    RTSStats (allocated_bytes, gc, gc_cpu_ns, gcs),
    getRTSStats,
    getRTSStatsEnabled,
 )
import qualified Options.Applicative as O
import System.CPUTime (getCPUTime)
import qualified System.Environment as Env
import System.Timeout (timeout)
import qualified Text.Read as TR

import Data.Containers.ListUtils (nubOrd)
import qualified Data.HashSet as HS
import System.IO (BufferMode (LineBuffering), hFlush, hPutStr, hPutStrLn, hSetBuffering, stderr)

data StEcta = StEcta
    { any_arg :: Node Symbol
    , eq_insts :: Map TypeSkeleton (T.Text, Value)
    , arb_insts :: Map TypeSkeleton (T.Text, Func)
    , sig_ty_cons :: [TypeSkeleton]
    , compl_sig :: Sig
    , given_sig :: Sig
    , phase_variables :: Map TypeSkeleton Symbol
    -- ^ The generated variable of each type of the phase.
    , inst_sig :: Sig
    {- ^ The complete signature with more variables of each
    type, for the instances of the schemas.
    -}
    , function_samples :: Map TypeSkeleton T.Text
    {- ^ With function buckets, the sample variable of each function type
    (see 'sigGivens'). The sample variables are in 'inst_sig'.
    -}
    , schema_vars :: Map Symbol [Symbol]
    {- ^ The variables of each type, from the variable with
    the index 0 of the type.
    -}
    , test_cases :: [Case]
    -- ^ The test cases that all terms of the phase share, with the values of the variables.
    , recheck_cases :: [Case]
    -- ^ The extra test cases of a new law (see 'recheckSchedule').
    }
    deriving (Show)

{- | The number of variables of each type that fill the holes of a schema.
QuickSpec uses 4 by default (@Use (UpTo 4)@).
-}
variablesPerType :: Int
variablesPerType = 4

{- | The largest schema that the search instantiates when the schema is a new
representative. Without it, the search does not find laws such as
commutativity, whose two sides have the same schema. QuickSpec uses 5
(@cfg_max_commutative_size@). The size of a term is the number of its
leaves, as in 'searchSpace'.
-}
maxCommutativeSize :: Int
maxCommutativeSize = 5

-- | Put the variables into the holes of a schema, from left to right.
fillHoles :: (Symbol -> Bool) -> [Symbol] -> Term -> Term
fillHoles isVar vars0 t0 = fst (go vars0 t0)
  where
    go vars (Term "app" [ty, f, v]) =
        let (f', vars') = go vars f
            (v', vars'') = go vars' v
         in (Term "app" [ty, f', v'], vars'')
    go (x : vars) (Term s tys) | isVar s = (Term x tys, vars)
    go vars t = (t, vars)

-- | The holes of a schema, from left to right. A hole is a variable.
holes :: (Symbol -> Bool) -> Term -> [Symbol]
holes isVar (Term "app" [_, f, v]) = holes isVar f ++ holes isVar v
holes isVar (Term s _) = [s | isVar s]

{- | The most general instance of a schema: each hole gets a different
variable of its type.
-}
mostGeneral :: (Symbol -> Bool) -> Map Symbol [Symbol] -> Term -> Term
mostGeneral isVar vars t = fillHoles isVar (snd (mapAccumL next Map.empty (holes isVar t))) t
  where
    next counts x =
        let n = Map.findWithDefault 0 x counts
         in (Map.insert x (n + 1) counts, (vars Map.! x) !! n)

{- | The instances of a schema: each hole gets one of the first
'variablesPerType' variables of its type. The instances with more
different variables come first, as in QuickSpec.
-}
schemaInstances :: (Symbol -> Bool) -> Map Symbol [Symbol] -> Term -> [Term]
schemaInstances isVar vars t =
    [ fillHoles isVar (map snd ivs) t
    | ivs <- sortOn generality (mapM (zip [0 :: Int ..] . take variablesPerType . (vars Map.!)) (holes isVar t))
    ]
  where
    generality ivs = (negate (length (nubOrd (map snd ivs))), map fst ivs)

{- | Give the variables of each type indexes in first-occurrence order.
Only the printed names change. Evaluation uses the original signature.
-}
canonicalLaw :: Sig -> Term -> Term
canonicalLaw sig law = rename law
  where
    variables =
        Map.fromList
            [(Symbol name, (ty, info)) | (name, GivenFun info@GivenVar{} ty) <- Map.assocs sig]
    occurrences (Term symbol children) = [symbol | symbol `Map.member` variables] ++ concatMap occurrences children
    names = Map.fromList (snd (mapAccumL next Map.empty (nubOrd (occurrences law))))
    next counts symbol =
        let (ty, GivenVar prefix label _ gen) = variables Map.! symbol
            index = Map.findWithDefault 0 ty counts
            name = Symbol (gvToName (GivenVar prefix label index gen))
         in (Map.insert ty (index + 1) counts, (symbol, name))
    rename (Term symbol children) = Term (Map.findWithDefault symbol symbol names) (map rename children)

termSize :: Term -> Int
termSize (Term s []) = 1
termSize (Term s [_]) = 1
termSize (Term s [_, f, v]) = 1 + termSize f + termSize v
termSize (Term s [f, v]) = 1 + termSize f + termSize v
termSize (Term s args) = 1 + sum (map termSize args)

-- if we find a rewrite from anything to a given var, it holds
-- for all things of that type! i.e. if x == x ++ [],
-- then we can rewrite all instances of (_ :: [A] ++ []) to (_::[A])
-- best would probably be to apply this in the node.

{- | Whether a pruning template leaves each type annotation open. Such a
template comes from a rule that rewrites each typing of a program, so it can
prune a skeleton before its typing is known.
-}
annotationFree :: Template Symbol -> Bool
annotationFree template = case template of
    Hole -> True
    TemplateNode "app" [Hole, _, f, x] -> annotationFree f && annotationFree x
    TemplateNode _ [Hole] -> True
    _ -> False

-- | Whether a symbol is a generated variable of the signature.
isGivenVar :: Sig -> Symbol -> Bool
isGivenVar sig (Symbol x) = case sig Map.!? x of
    Just (GivenFun{given_info = GivenVar{}}) -> True
    _ -> False

-- | The state of the search. The phases and the sizes share it.
data Search = Search
    { seen :: !(HS.HashSet Term)
    -- ^ The terms that the search does not test again.
    , trees :: !(Map Term DT.DecisionTree)
    -- ^ The decision tree of the representative schemas of each type.
    , instance_trees :: !(Map Term DT.DecisionTree)
    -- ^ The decision tree of the instances of each representative schema.
    , instantiated :: !(HS.HashSet Term)
    -- ^ The representative schemas whose instances are in their trees.
    , rewrite_rules :: !Rules
    -- ^ The rules of the laws, by the heads of their left sides.
    , so_far :: !Int
    -- ^ The number of terms that the search examined.
    , law_count :: !Int
    -- ^ The number of laws that the search found.
    , pending_laws :: ![(Term, Term, Sig, Term)]
    {- ^ With 'deferLaws', the laws of a bucket, newest first: the two terms
    of the test, and the signature and the law that 'generalizeLaw' gives.
    -}
    , touched_reps :: !(HS.HashSet Term)
    -- ^ The representatives whose instance trees a bucket changed.
    }

-- | The settings of the search, which do not change.
data Settings = Settings
    { progress :: Bool
    -- ^ Whether to show the progress on stderr.
    , numTests :: Int
    -- ^ The number of test cases that the terms of a phase share.
    , maxSize :: Int
    -- ^ The largest size of the terms of the search.
    , diagnostics :: Bool
    -- ^ Whether to emit flushed timing events on stderr.
    , detailedDiagnostics :: Bool
    -- ^ Whether to include stages inside each bucket.
    , resolveInstance :: TypeSkeleton -> Maybe Instance
    -- ^ Resolve exact generators and equality for law generalization.
    , diagnosticPhase :: Int
    -- ^ The phase that is running, rather than the requested last phase.
    , stopAfter :: Maybe (Int, Int)
    , onlyBucket :: Maybe String
    {- ^ With 'stopAfter', the only bucket of the last size, by the 'show' of
    its type; each of its schemas prints its time and its term (spike).
    -}
    , -- \^ The phase and the size after which the search stops, for a profile
      --    of a part of a long run.
      --
      splitEnumeration :: Int
    , skeletonTemplates :: Bool
    -- ^ Whether the templates of the rules prune the skeletons (spike).
    , parallelBuckets :: Bool
    {- ^ Whether the buckets of a size run in parallel from the state at the
    start of the size (spike).
    -}
    , enumerateAhead :: Bool
    {- ^ Whether phase 4 enumerates the skeletons of all the types of a size
    in background threads at the start of the size, while the buckets test
    in order (spike).
    -}
    , bucketTimeout :: Maybe Double
    -- ^ The seconds after which a bucket stops testing its schemas.
    , bucketMemLimit :: Maybe Word64
    , completionTimeout :: Maybe Double
    -- ^ The seconds that the completion of one law may take.
    , completionMemLimit :: Word64
    -- ^ The bytes by which the completion of one law may grow the live heap.
    , recheckCount :: Int
    -- ^ The number of extra test cases of a new law (see 'recheckSchedule').
    , typeDepth :: Maybe Int
    {- ^ The largest depth of the type of a type variable of the grammar (see
    'mtauWithin'). 'Nothing' is no limit.
    -}
    , functionBuckets :: Bool
    {- ^ Whether each function type between two small data types of the
    signature gets a bucket (see 'sigGivens').
    -}
    , dumpLaws :: Bool
    -- ^ Whether to write each law with the types of its subterms on stderr.
    , completionAllocLimit :: Word64
    {- ^ The bytes that the completion of one law may allocate.
    ^ The bytes by which a bucket may grow the live heap.
    -}
    , lawSink :: IORef [(Term, Term, Sig, Term)]
    {- ^ With 'deferLaws', the laws of the schema that runs, newest first, so
    that a schema that runs out of time keeps the laws that it found.
    -}
    , deferLaws :: Bool
    {- ^ Whether a bucket records its laws in 'pending_laws' instead of
    printing them.
    -}
    }

-- \^ Whether to enumerate the skeletons of a bucket in one thread for each
--    shape of the left spine (spike).
--

{- | Emit one versioned TSV event. Allocation and GC counters are RTS
samples. This function does not force a collection or inspect test values.
-}
diagnosticEvent :: Settings -> String -> Int -> String -> String -> Search -> IO ()
diagnosticEvent Settings{diagnostics = False} _ _ _ _ _ = return ()
diagnosticEvent Settings{..} event level ty stage s = do
    wall <- getMonotonicTimeNSec
    cpu <- getCPUTime
    enabled <- getRTSStatsEnabled
    stats <- if enabled then Just <$> getRTSStats else return Nothing
    hPutStrLn stderr $
        intercalate
            "\t"
            [ "specftacular-diagnostic"
            , "1"
            , event
            , show diagnosticPhase
            , show level
            , stage
            , ty
            , show wall
            , show cpu
            , if event == "begin" || event == "checkpoint" then show (so_far s) else ""
            , if event == "begin" || event == "checkpoint" then show (law_count s) else ""
            , maybe "" (show . allocated_bytes) stats
            , maybe "" (show . gc_cpu_ns) stats
            , maybe "" (show . gcs) stats
            ]
    hFlush stderr

{- | Measure demanded IO work. An abort event preserves the active stage
when cancellation propagates. Nested intervals include their children.
-}
diagnose :: Settings -> Int -> String -> String -> Search -> IO a -> IO a
diagnose env@Settings{..} level ty stage s action
    | not diagnostics || not detailedDiagnostics && stage `notElem` ["phase", "bucket"] = action
    | otherwise = mask $ \restore -> do
        diagnosticEvent env "begin" level ty stage s
        result <- restore action `onException` diagnosticEvent env "abort" level ty stage s
        diagnosticEvent env "end" level ty stage s
        return result

-- | The options of a search.
data SearchOptions = SearchOptions
    { searchSize :: Int
    -- ^ The largest size of the terms.
    , searchPhase :: Int
    -- ^ The last phase, from 1 to 4.
    , searchParallel :: Bool
    -- ^ Whether the buckets of a size run in parallel. This needs @+RTS -N@.
    , searchEnumerateAhead :: Bool
    {- ^ Whether phase 4 enumerates the skeletons of the types of a size in
    background threads, while the buckets test in order. This needs
    @+RTS -N@.
    -}
    , searchSplit :: Int
    {- ^ The number of levels of applications by which phase 4 splits the
    enumeration of its skeletons into parts of one shape (0: no split).
    -}
    , searchBucketTimeout :: Maybe Double
    {- ^ The seconds after which a bucket stops testing its schemas. The
    search reports the bucket and goes on with the next one.
    -}
    , searchBucketMemLimit :: Maybe Word64
    {- ^ The bytes by which a bucket may grow the live heap. Over them, the
    bucket stops testing its schemas, as after 'searchBucketTimeout'.
    -}
    , searchCompletionTimeout :: Maybe Double
    {- ^ The seconds that the completion of one law may take. Over them, the
    law keeps only its own rules (see 'boundedCompletion').
    -}
    , searchCompletionMemLimit :: Word64
    -- ^ The bytes by which the completion of one law may grow the live heap.
    , searchCompletionAllocLimit :: Word64
    -- ^ The bytes that the completion of one law may allocate.
    , searchRecheck :: Int
    {- ^ The number of extra test cases of small sizes on which a new law is
    tested again (0: no test). The search drops a law that one of them
    refutes. At HugeLists 6-p4, 2000 of them refute the 4 false laws that
    pass the cases of 'testSchedule'.
    -}
    , searchTests :: Int
    -- ^ The number of random test cases (1000, as in QuickSpec).
    , searchChecked :: Bool
    {- ^ Whether the values keep their types, so that each application tests
    them (see 'Value').
    -}
    , searchProgress :: Bool
    -- ^ Whether to show the progress of the search on stderr.
    , searchDiagnostics :: Maybe Diagnostics
    -- ^ The diagnostic events on stderr, if any (see 'diagnosticEvent').
    , searchSkeletonTemplates :: Bool
    -- ^ Whether the templates of the rules prune the phase 4 skeletons.
    , searchStopAfter :: Maybe (Int, Int)
    {- ^ The phase and the size after which the search stops, so that a
    profile of the run is written.
    -}
    , searchOnlyBucket :: Maybe String
    {- ^ With 'searchStopAfter', the only bucket of the last size, by the
    'show' of its type. Each of its schemas prints its time and its term.
    -}
    , searchTypeDepth :: Maybe Int
    {- ^ The largest depth of the type of a type variable of the grammar.
    'Nothing' is no limit.
    -}
    , searchFunctionBuckets :: Bool
    {- ^ Whether each function type between two small data types of the
    signature gets a bucket. Each test case applies two functions to a
    sample of their argument type and compares the results.
    -}
    , searchDumpLaws :: Bool
    -- ^ Whether to write each law with the types of its subterms on stderr.
    }
    deriving (Show)

-- | The diagnostic events that a search writes on stderr, as versioned TSV.
data Diagnostics
    = -- | The phases and the buckets.
      PhaseDiagnostics
    | -- | The stages inside each bucket too.
      DetailedDiagnostics
    deriving (Eq, Show)

-- | A sequential search with terms up to a size and the phases up to a phase.
defaultOptions :: Int -> Int -> SearchOptions
defaultOptions size phase =
    SearchOptions
        { searchSize = size
        , searchPhase = phase
        , searchParallel = False
        , searchEnumerateAhead = False
        , searchSplit = 2
        , searchBucketTimeout = Nothing
        , searchBucketMemLimit = Nothing
        , searchCompletionTimeout = Nothing
        , searchCompletionMemLimit = completionMemoryLimit
        , searchCompletionAllocLimit = completionBudget
        , searchRecheck = 0
        , searchTests = 1000
        , searchChecked = False
        , searchProgress = False
        , searchDiagnostics = Nothing
        , searchSkeletonTemplates = True
        , searchStopAfter = Nothing
        , searchOnlyBucket = Nothing
        , searchTypeDepth = Nothing
        , searchFunctionBuckets = False
        , searchDumpLaws = False
        }

{- | Read the options from the program arguments: the size, the phase,
@--parallel@, @--enumerate-ahead@, @--split DEPTH@, the limits of a bucket
(@--bucket-timeout SECONDS@, @--bucket-mem-limit SIZE@), and the limits of the
completion of one law (@--completion-timeout SECONDS@,
@--completion-mem-limit SIZE@, @--completion-alloc-limit SIZE@). The split is
2, unless @--split@ gives it.
-}
parseOptions :: IO SearchOptions
parseOptions = O.execParser (O.info (options O.<**> O.helper) (O.fullDesc <> O.progDesc "Find the laws of a signature."))
  where
    -- The parsers are in the order of the fields of 'SearchOptions'.
    options =
        SearchOptions
            <$> size
            <*> phase
            <*> parallel
            <*> ahead
            <*> split
            <*> O.optional bucketTimeout
            <*> O.optional bucketMemLimit
            <*> O.optional completionTimeoutOption
            <*> completionMemLimitOption
            <*> completionAllocLimitOption
            <*> recheckOption
            <*> testsOption
            <*> O.switch (O.long "checked" <> O.help "Keep the types of the values, and test them at each application")
            <*> O.switch (O.long "progress" <> O.help "Show the progress of the search on stderr")
            <*> O.optional diagnosticsOption
            <*> ( not
                    <$> O.switch (O.long "no-skeleton-templates" <> O.help "Enumerate the phase 4 skeletons without the templates of the rules")
                )
            <*> O.optional stopAfterOption
            <*> O.optional
                ( O.strOption
                    ( O.long "only-bucket"
                        <> O.metavar "TYPE"
                        <> O.help "With --stop-after, run only this bucket at the last size, and time each of its schemas"
                    )
                )
            <*> O.optional
                ( O.option
                    O.auto
                    ( O.long "type-depth"
                        <> O.metavar "D"
                        <> O.help "Bound the types that the type variables of the grammar take to depth D"
                    )
                )
            <*> O.switch
                ( O.long "function-buckets"
                    <> O.help
                        "Give a bucket to each function type between two small data types, and compare two functions on a sample of their argument type in each test case"
                )
            <*> O.switch (O.long "dump-laws" <> O.help "Write each law with the types of its subterms on stderr")
    testsOption =
        O.option
            O.auto
            ( O.long "tests"
                <> O.metavar "N"
                <> O.value 1000
                <> O.help "The number of random test cases (default 1000, as in QuickSpec)"
            )
    diagnosticsOption =
        O.option
            (O.maybeReader (`lookup` [("phases", PhaseDiagnostics), ("detailed", DetailedDiagnostics)]))
            ( O.long "diagnostics"
                <> O.metavar "phases|detailed"
                <> O.help "Write the events of the phases and the buckets, or also of the stages inside each bucket, on stderr"
            )
    stopAfterOption =
        O.option
            (O.maybeReader parseStop)
            (O.long "stop-after" <> O.metavar "PHASE:SIZE" <> O.help "Stop the search after this size of this phase")
    size = O.argument O.auto (O.metavar "SIZE" <> O.help "The largest size of the terms")
    phase = O.argument O.auto (O.metavar "PHASE" <> O.help "The last phase, from 1 to 4")
    parallel =
        O.switch
            ( O.long "parallel"
                <> O.help "Run the buckets of a size in parallel, and enumerate the phase 4 skeletons in parallel parts (needs +RTS -N)"
            )
    ahead =
        O.switch
            ( O.long "enumerate-ahead"
                <> O.help
                    "Enumerate the phase 4 skeletons of all the types of a size in background threads, and test the buckets in order (needs +RTS -N)"
            )
    split =
        O.option
            O.auto
            ( O.long "split"
                <> O.metavar "DEPTH"
                <> O.value 2
                <> O.help
                    "Split the phase 4 skeletons by shape down to DEPTH levels of applications (default 2; 0 does not split)"
            )
    bucketTimeout =
        O.option
            O.auto
            ( O.long "bucket-timeout"
                <> O.metavar "SECONDS"
                <> O.help
                    "Stop testing the schemas of a bucket after SECONDS, report the bucket, and go on (the laws then depend on the speed of the machine)"
            )
    bucketMemLimit =
        O.option
            (O.maybeReader parseBytes)
            ( O.long "bucket-mem-limit"
                <> O.metavar "SIZE"
                <> O.help
                    "Stop testing the schemas of a bucket when it grows the live heap by more than SIZE (such as 512M or 4G), report the bucket, and go on (needs RTS statistics, +RTS -T; the laws then depend on the times of the collections)"
            )
    completionTimeoutOption =
        O.option
            O.auto
            ( O.long "completion-timeout"
                <> O.metavar "SECONDS"
                <> O.help
                    "Keep only the rules of a law whose completion takes more than SECONDS (no limit by default; the laws then depend on the speed of the machine)"
            )
    completionMemLimitOption =
        O.option
            (O.maybeReader parseBytes)
            ( O.long "completion-mem-limit"
                <> O.metavar "SIZE"
                <> O.value completionMemoryLimit
                <> O.help
                    "Keep only the rules of a law whose completion grows the live heap by more than SIZE (default 4G; needs RTS statistics, +RTS -T; the laws then depend on the times of the collections)"
            )
    completionAllocLimitOption =
        O.option
            (O.maybeReader parseBytes)
            ( O.long "completion-alloc-limit"
                <> O.metavar "SIZE"
                <> O.value completionBudget
                <> O.help "Keep only the rules of a law whose completion allocates more than SIZE (default 256G)"
            )
    recheckOption =
        O.option
            O.auto
            ( O.long "recheck"
                <> O.metavar "N"
                <> O.value 0
                <> O.help "Test each new law again on N random cases of sizes 1 to 8, and drop it if one refutes it (default 0: no test)"
            )

-- | The exception that 'withMemoryLimit' throws to its thread.
newtype MemoryLimitHit = MemoryLimitHit Unique
    deriving (Eq)

instance Show MemoryLimitHit where
    show _ = "<<bucket memory limit>>"

instance Exception MemoryLimitHit where
    toException = asyncExceptionToException
    fromException = asyncExceptionFromException

-- | The live bytes of the heap after the last collection.
liveBytes :: IO Word64
liveBytes = gcdetails_live_bytes . gc <$> getRTSStats

{- | Run an action, and stop it when the live heap grows by more than a
number of bytes over a base: 'Left' gives the growth. A thread reads the
statistics of the collector every 100 ms, so the stop comes after the
collection that sees the growth.
-}
withMemoryLimit :: Maybe (Word64, Word64) -> IO a -> IO (Either Word64 a)
withMemoryLimit Nothing action = Right <$> action
withMemoryLimit (Just (base, bytes)) action = do
    me <- myThreadId
    key <- newUnique
    grown <- newIORef 0
    let hit = MemoryLimitHit key
        watch = do
            threadDelay 100000
            live <- liveBytes
            if live > base + bytes
                then writeIORef grown (live - base) >> throwTo me hit
                else watch
    handleJust
        (\e -> if e == hit then Just () else Nothing)
        (\_ -> Left <$> readIORef grown)
        (bracket (forkIOWithUnmask (\unmask -> unmask watch)) (uninterruptibleMask_ . killThread) (\_ -> Right <$> action))

-- | Read a number of bytes with an optional suffix K, M, G, or T (powers of 1024).
parseBytes :: String -> Maybe Word64
parseBytes text = case span (`elem` ['0' .. '9']) text of
    (digits@(_ : _), suffix) -> (read digits *) <$> lookup suffix units
    _ -> Nothing
  where
    units = [("", 1), ("K", 1024), ("M", 1024 ^ (2 :: Int)), ("G", 1024 ^ (3 :: Int)), ("T", 1024 ^ (4 :: Int))]

{- | Print the laws of a signature, with terms up to the size that the first
program argument gives (6 by default). The types are monomorphic, as in
'discoverMonomorphic'.
-}
ftacularSpec :: [Sig] -> IO ()
ftacularSpec sigs =
    do
        args <- Env.getArgs
        let size = case args of
                arg : _ | Just n <- TR.readMaybe arg -> n
                _ -> 6
        _ <- discoverMonomorphic size (const Nothing) sigs
        return ()

{- | The laws of a signature with terms up to a size. The types are
monomorphic: A, B, C, D, and Acc all become A (phase 1). The function
gives the generators and the equalities of other types.
-}
discoverMonomorphic :: Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> [Sig] -> IO [String]
discoverMonomorphic size = experimentalPhases (defaultOptions size 1)

{- | The laws of a signature, with the phases from 1 to the given phase.
Phases 2 to 4 are experimental. Phase 2 keeps A, B, C, D, and Acc apart.
Phases 3 and 4 instantiate the abstract carrier types of each constant.
The search checks every instance before evaluation (see 'termType').
-}
experimentalPhases :: SearchOptions -> (TypeSkeleton -> Maybe GeneratedInstance) -> [Sig] -> IO [String]
experimentalPhases options extraReps sigs = searchPhases options (frontInstances extraReps) (mconcat sigs)

{- | 'experimentalPhases' with the instances of the types for the search,
for a front end that does not give the types of the values to Haskell,
such as a GHC session.
-}
searchPhases :: SearchOptions -> (TypeSkeleton -> Maybe Instance) -> Sig -> IO [String]
searchPhases
    SearchOptions
        { searchSize = size
        , searchPhase = phase
        , searchParallel = parallelSetting
        , searchEnumerateAhead = aheadSetting
        , searchSplit = splitSetting
        , searchBucketTimeout = timeoutSetting
        , searchBucketMemLimit = memLimitOption
        , searchCompletionTimeout = completionTimeoutSetting
        , searchCompletionMemLimit = completionMemLimitSetting
        , searchCompletionAllocLimit = completionAllocLimitSetting
        , searchRecheck = recheckSetting
        , searchTests = numTests
        , searchChecked = checked
        , searchProgress = progress
        , searchDiagnostics = diagnosticSetting
        , searchSkeletonTemplates = skeletonTemplatesSetting
        , searchStopAfter = stopSetting
        , searchOnlyBucket = onlySetting
        , searchTypeDepth = typeDepthSetting
        , searchFunctionBuckets = functionBucketsSetting
        , searchDumpLaws = dumpLawsSetting
        }
    givenInstances
    givenSig =
        do
            -- Threads write whole diagnostic lines.
            when parallelSetting $ hSetBuffering stderr LineBuffering
            sink <- newIORef []
            statsEnabled <- getRTSStatsEnabled
            let memLimitSetting = if statsEnabled then memLimitOption else Nothing
            when (isJust memLimitOption && not statsEnabled) $
                hPutStrLn stderr "*** Warning: --bucket-mem-limit needs RTS statistics (+RTS -T); it has no effect."
            when (isJust memLimitSetting && aheadSetting) $
                hPutStrLn
                    stderr
                    "*** Warning: with --enumerate-ahead, --bucket-mem-limit also counts the heap of the background enumeration."
            let diagnostics = isJust diagnosticSetting
                detailedDiagnostics = diagnosticSetting == Just DetailedDiagnostics
                sig
                    | checked = givenSig
                    | otherwise = untypedSig givenSig
                instances
                    | checked = givenInstances
                    | otherwise = fmap untypedInstance . givenInstances
            let StEcta
                    { compl_sig = compl_sig
                    , arb_insts = arb_insts
                    , sig_ty_cons = sig_ty_cons
                    } = mkStecta size numTests 0 typeDepthSetting functionBucketsSetting instances sig False id id
            putStrLn $ "In Scope (" ++ show (Map.size compl_sig) ++ " functions/constants):"
            putStrLn "---------------------------------"
            mapM_ (putStrLn . T.unpack) $ Map.keys compl_sig
            putStrLn ""
            putStrLn "Type constructors (and derived) in the signature:"
            putStrLn "---------------------------------"
            mapM_ print sig_ty_cons
            putStrLn ""
            putStrLn "Variable generators"
            putStrLn "---------------------------------"
            mapM_ print (Map.assocs arb_insts)
            putStrLn ""

            putStrLn "Laws according to Haskell's (==):"
            putStrLn "---------------------------------"
            let env =
                    Settings
                        { progress = progress
                        , numTests = numTests
                        , maxSize = size
                        , diagnostics = diagnostics
                        , detailedDiagnostics = detailedDiagnostics
                        , diagnosticPhase = 0
                        , resolveInstance = instances
                        , splitEnumeration = splitSetting
                        , skeletonTemplates = skeletonTemplatesSetting
                        , parallelBuckets = parallelSetting
                        , enumerateAhead = aheadSetting
                        , deferLaws = parallelSetting || isJust timeoutSetting || isJust memLimitSetting
                        , bucketMemLimit = memLimitSetting
                        , bucketTimeout = timeoutSetting
                        , completionTimeout = completionTimeoutSetting
                        , completionMemLimit = completionMemLimitSetting
                        , completionAllocLimit = completionAllocLimitSetting
                        , recheckCount = recheckSetting
                        , lawSink = sink
                        , stopAfter = stopSetting
                        , onlyBucket = onlySetting
                        , typeDepth = typeDepthSetting
                        , functionBuckets = functionBucketsSetting
                        , dumpLaws = dumpLawsSetting
                        }
            runPhases env size (max 1 (min 4 phase)) instances sig

-- | Read "phase:size".
parseStop :: String -> Maybe (Int, Int)
parseStop text = case break (== ':') text of
    (phase, ':' : size) -> (,) <$> TR.readMaybe phase <*> TR.readMaybe size
    _ -> Nothing

-- 1. The runtime signature and the search space.

{- | The runtime signature and the search space of one phase: the signature
with the generated variables and the equalities, the node of the atoms,
and the types to test. With 'True', the generated variables also have
each renaming of the carriers of their types (see 'sigGivens'). The first
function changes the types of the generated variables, and the second the
types of the functions.
-}
mkStecta ::
    Int ->
    Int ->
    Int ->
    Maybe Int ->
    Bool ->
    (TypeSkeleton -> Maybe Instance) ->
    Sig ->
    Bool ->
    (TypeSkeleton -> TypeSkeleton) ->
    (TypeSkeleton -> TypeSkeleton) ->
    StEcta
mkStecta size numTests recheckCount typeDepth' functionBuckets' instances sig closed givenTrans skelTrans =
    StEcta
        { any_arg = ag
        , compl_sig = compl_sig
        , given_sig = givenSig
        , phase_variables = Map.fromList [(sfTypeRep f, Symbol name) | (name, f) <- Map.assocs givenSig]
        , inst_sig = inst_sig
        , function_samples = fst <$> samples
        , schema_vars = Map.fromList [(Symbol x, map (Symbol . fst) vs) | (x, vs) <- moreVars]
        , sig_ty_cons = Map.keys eq_insts
        , eq_insts = eq_insts
        , test_cases = withValues inst_sig (testSchedule numTests)
        , recheck_cases = withValues inst_sig (recheckSchedule recheckCount)
        , arb_insts = arbs
        }
  where
    skels = Map.assocs $ skelTrans . sfTypeRep <$> sig
    -- The most general instance of a schema of the given size has at
    -- most size variables of a type.
    moreVars =
        [ (x, [(gvToName gv, g) | g@(GivenFun gv _) <- take (max variablesPerType size) (moreGenerators f)])
        | (x, f@(GivenFun{given_info = GivenVar{}})) <- Map.assocs compl_sig
        ]
    inst_sig = Map.fromList (concatMap snd moreVars) <> Map.fromList (Map.elems samples) <> compl_sig
    (givenSig, eq_insts, arbs, samples) = sigGivens closed functionBuckets' givenTrans sig instances
    givens = Map.assocs $ givenTrans . sfTypeRep <$> givenSig
    compl_sig = sig <> givenSig
    sc = skels ++ givens
    ag =
        Node
            $ map (\(s, t) -> Edge s [t])
            $
            -- we generalize the functions in the signature but not
            -- This means we don't select givens as candidates
            -- for application which is what we want, we don't
            -- want to apply variables to each other.
            ngnodes givens ++ gnodes skels
    addSyms st tt = map (Bi.bimap (Symbol . st) (tt . typeToFta))
    ngnodes = addSyms id id
    gnodes = addSyms id (generalize typeDepth' sc)

{- | The phases: the message at the end of the phase, the message at the
start of the phase, the changes of the types of the generated variables and
of the functions, and the change of the types of the variables of a
skeleton grammar. A phase with a skeleton grammar does not enumerate its own
grammar. It tests the most general carrier typing of each schema of the
skeleton grammar instead (see 'generalizeCarriers'). Phase 4 enumerates
with its functions and with variables at A, so the constants keep
independent type variables and the variables of a skeleton are fewer.
-}
phases ::
    [(String, String, TypeSkeleton -> TypeSkeleton, TypeSkeleton -> TypeSkeleton, Maybe (TypeSkeleton -> TypeSkeleton))]
phases =
    [ ("Fully monomorphic phase finished..", "", monomorphiseType, monomorphiseType, Nothing)
    , ("Monomorphic phases finished..", "Starting phase with more types....", id, id, Nothing)
    ,
        ( "Mono-polymorphic phase done! "
        , "Starting mono-polymorphic phase...."
        , monomorphiseType
        , generalizeType . monomorphiseType
        , Nothing
        )
    , ("Done! ", "Starting fully-polymorphic phase....", id, generalizeType, Just monomorphiseType)
    ]

{- | Run the phases from 1 to the given phase. The search state goes from
one phase to the next.
-}
runPhases :: Settings -> Int -> Int -> (TypeSkeleton -> Maybe Instance) -> Sig -> IO [String]
runPhases env size lastPhase instances sig =
    go
        (zip [1 ..] phases)
        Search
            { seen = HS.empty
            , trees = Map.empty
            , instance_trees = Map.empty
            , instantiated = HS.empty
            , rewrite_rules = emptyRules
            , so_far = 0
            , law_count = 0
            , pending_laws = []
            , touched_reps = HS.empty
            }
  where
    go ((pn, (finished, starting, givenTrans, skelTrans, skeletonTrans)) : rest) s
        | pn <= lastPhase = do
            when (pn > 1) $ putStrLn starting
            let phaseEnv = env{diagnosticPhase = pn}
                -- A phase with a skeleton grammar closes its variable types
                -- under carrier renaming, so each renaming of a typing of a
                -- skeleton has its variables.
                stectaWith variableTrans =
                    mkStecta
                        size
                        (numTests env)
                        (recheckCount env)
                        (typeDepth env)
                        (functionBuckets env)
                        instances
                        sig
                        (isJust skeletonTrans)
                        variableTrans
                        skelTrans
            (laws, s') <- diagnose phaseEnv 0 "" "phase" s $ do
                result@(_, finishedState) <- runPhase phaseEnv (phaseSize pn) (stectaWith <$> skeletonTrans) (stectaWith givenTrans) s
                diagnosticEvent phaseEnv "checkpoint" 0 "" "phase" finishedState
                return result
            putStrLn $ finished ++ show (so_far s') ++ " terms examined."
            putStrLn $ show (sum $ map DT.size $ Map.elems (trees s')) ++ " unique terms discovered."
            if fmap fst (stopAfter env) == Just pn then return laws else (laws ++) <$> go rest s'
    go _ _ = return []
    phaseSize pn = case stopAfter env of
        Just (stopPhase, stopSize) | stopPhase == pn -> min size stopSize
        _ -> size

{- | Run one phase: the sizes from 1 to the given size, and for each size
each type to test. With a skeleton grammar, the candidates of a type are the
most general carrier typings with that result type of the skeletons of its
monomorphic type.
-}
runPhase :: Settings -> Int -> Maybe StEcta -> StEcta -> Search -> IO ([String], Search)
runPhase env@Settings{..} size skeletons stecta@StEcta{..}
    | parallelBuckets = goSizes [1 .. size]
    | otherwise = go Map.empty [(lvl, tc) | lvl <- [1 .. size], tc <- ordered, kept lvl tc]
  where
    kept lvl tc = case (onlyBucket, stopAfter) of
        (Just only, Just (stopPhase, stopSize)) | stopPhase == diagnosticPhase && stopSize == lvl -> show tc == only
        _ -> True
    ordered = sortOn (\t -> (typeSize t, concreteTypeLeaves t, t)) (filter tested sig_ty_cons)
    -- With 'parallelBuckets', the buckets of a size run in parallel from the
    -- state at the start of the size. A bucket changes only the trees of its
    -- type and records its laws. The merge takes the trees of each bucket,
    -- and adds its laws in the order of the buckets. It drops a law that the
    -- laws before it prove. Each printed law passed its tests.
    goSizes [] s = return ([], s)
    goSizes (lvl : rest) s = do
        typings <- case skeletons of
            Just skeleton ->
                Map.fromList
                    <$> concurrently
                        [ do
                            found <- skeletonTypings skeleton lvl key (rewrite_rules s)
                            _ <- evaluate (length found)
                            pure (key, found)
                        | key <- nubOrd (map monomorphiseType ordered)
                        ]
            Nothing -> pure Map.empty
        results <-
            concurrently
                [ diagnose env lvl (show tc) "bucket" s $
                    bucket lvl (Map.lookup (monomorphiseType tc) typings) tc s{pending_laws = [], touched_reps = HS.empty}
                | tc <- ordered
                ]
        (laws, s') <- foldM (mergeBucket s) ([], s) (zip ordered results)
        (more, s'') <- goSizes rest s'
        return (laws ++ more, s'')
    mergeBucket start (laws, merged) (tc, (_, done)) = do
        let key = typeSkeletonToTerm tc
            combined =
                merged
                    { seen = HS.union (seen done) (seen merged)
                    , trees = maybe (trees merged) (\tree -> Map.insert key tree (trees merged)) (Map.lookup key (trees done))
                    , instance_trees =
                        foldl'
                            (\m r -> maybe m (\tree -> Map.insert r tree m) (Map.lookup r (instance_trees done)))
                            (instance_trees merged)
                            (HS.toList (touched_reps done))
                    , instantiated = HS.union (instantiated done) (instantiated merged)
                    , so_far = so_far merged + so_far done - so_far start
                    }
        foldM replay (laws, combined) (reverse (pending_laws done))
    replay (laws, s) (w, i, lawSig, law)
        | joinable (isGivenVar inst_sig) (rewrite_rules s) w i = return (laws, s)
        | otherwise = do
            let n = law_count s + 1
                lawText = show n <> ". " <> ppNpTerm (canonicalLaw lawSig law)
            putStrLn lawText
            rules <-
                boundedCompletion env lawText (addLaw maxSize lawSig law (rewrite_rules s)) (addLawRules lawSig law (rewrite_rules s))
            return (laws ++ [lawText], s{law_count = n, rewrite_rules = rules})
    -- With a skeleton grammar, the variable types are closed under carrier
    -- renaming (see 'mkStecta'). Then the schemas of a type are the
    -- renamings of the schemas of its canonical type (see
    -- 'generalizeCarriers'), and the canonical type finds their laws up to
    -- renaming. This needs variables whose carriers are the first carriers
    -- of 'carriers'.
    tested tc = case skeletons of
        Just _
            | firstCarriers ->
                canonicalCarrierType tc == tc || canonicalCarrierType tc `notElem` sig_ty_cons
        _ -> True
    firstCarriers =
        let used = nubOrd (concatMap carriersOf (Map.keys phase_variables))
         in sort used == sort (take (length used) (map fst carriers))
    -- Only program applications have this shape. Do not exclude matching
    -- type constructors in a custom signature.
    canPrune = ("app", 4) `notElem` allConstructors (Map.assocs (sfTypeRep <$> compl_sig))
    go _ [] s = return ([], s)
    go cache ((lvl, tc) : rest) s = do
        -- A typing of a skeleton with the result type has the monomorphic
        -- result type in the skeleton grammar. The first bucket of a size and
        -- a monomorphic type finds the typings of its skeletons. The later
        -- buckets of the size with that monomorphic type use them again, and
        -- 'eligible' applies the rules that the buckets between them add.
        let key = monomorphiseType tc
            current = Map.filterWithKey (\(size', _) _ -> size' == lvl) cache
        cache' <- case skeletons of
            Just skeleton
                | Map.notMember (lvl, key) current ->
                    if enumerateAhead
                        then do
                            -- The first bucket of a size starts the enumeration of
                            -- the skeletons of each type of the size. The rules at
                            -- the start of the size prune them, and 'eligible'
                            -- applies the rules that the buckets add later.
                            let keys = nubOrd [monomorphiseType tc' | (lvl', tc') <- (lvl, tc) : rest, lvl' == lvl]
                            started <- enumerateInBackground [skeletonParts skeleton lvl k (rewrite_rules s) | k <- keys]
                            pure (Map.union (Map.fromList (zip [(lvl, k) | k <- keys] started)) current)
                        else do
                            typings <- skeletonTypings skeleton lvl key (rewrite_rules s)
                            pure (Map.insert (lvl, key) (pure (), typings) current)
            _ -> pure current
        let entry = Map.lookup (lvl, key) cache'
        mapM_ fst entry
        (laws, s') <- diagnose env lvl (show tc) "bucket" s $ do
            result@(_, finishedState) <- bucket lvl (snd <$> entry) tc s
            diagnosticEvent env "checkpoint" lvl (show tc) "bucket" finishedState
            return result
        (more, s'') <- go cache' rest s'
        return (laws ++ more, s'')
    -- The principal typings of the skeletons of a size and a monomorphic type
    -- (see 'generalizeCarriers'). Only templates without annotations prune a
    -- skeleton, because they match each typing of it.
    -- With 'splitEnumeration', each shape of the left spine is enumerated and
    -- typed in its own thread, and the parts are joined in their order.
    skeletonTypings skeleton lvl monomorphic rules
        | splitEnumeration > 0 =
            concat <$> forceInParallel diagnostics lvl monomorphic (skeletonParts skeleton lvl monomorphic rules)
        | otherwise = pure (concat (skeletonParts skeleton lvl monomorphic rules))
    -- The typings of the parts of the skeletons, in their order.
    skeletonParts skeleton@StEcta{compl_sig = skeletonSig} lvl monomorphic rules
        | splitEnumeration > 0 = map typingsOf (searchSpaceParts splitEnumeration skeleton lvl monomorphic)
        | otherwise = [typingsOf (searchSpace skeleton lvl monomorphic)]
      where
        templates
            | canPrune && skeletonTemplates = filter annotationFree (pruningTemplates skeletonSig lvl rules)
            | otherwise = []
        typingsOf space =
            let (pruningRoot, oracleTemplates) = preparePruning templates (refold space)
             in mapMaybe (generalizeCarriers skeletonSig phase_variables . npTerm') (prunedTerms oracleTemplates pruningRoot)
    bucket lvl typings tc s = do
        bucketStart <- getMonotonicTimeNSec
        let bucketTemplates
                | canPrune = pruningTemplates compl_sig lvl (rewrite_rules s)
                | otherwise = []
        produced <- case typings of
            Just typingsOfType -> pure $ nubOrd (mapMaybe ($ tc) typingsOfType)
            Nothing
                | splitEnumeration > 0 ->
                    -- Each shape of the spine is reduced and enumerated on its own,
                    -- as for the phase 4 skeletons (see 'spineParts').
                    pure
                        [ canonicalTypes (npTerm' t)
                        | space <- searchSpaceParts splitEnumeration stecta lvl tc
                        , let (pruningRoot, oracleTemplates) = preparePruning bucketTemplates (refold space)
                        , t <- prunedTerms oracleTemplates pruningRoot
                        ]
            Nothing -> do
                refreshCount progress "Reducing  ECTA" (" for " ++ show tc) "" lvl (so_far s)
                reduced <- diagnose env lvl (show tc) "reduce_whnf" s $ evaluate (searchSpace stecta lvl tc)
                refreshCount progress "Refolding ecta" (" for " ++ show tc) "" lvl (so_far s)
                folded <- diagnose env lvl (show tc) "refold_whnf" s $ evaluate (refold reduced)
                -- The oracle rejects partial branches before their remaining type
                -- choices expand. The bucket has one program size. KBO orders its
                -- ties before testing; smaller sizes have already supplied rules.
                let (pruningRoot, oracleTemplates) = preparePruning bucketTemplates folded
                pure [canonicalTypes (npTerm' t) | t <- prunedTerms oracleTemplates pruningRoot]
        let terms = sortBy (kboCompare (isGivenVar compl_sig)) (filter eligible produced)
            -- Apply the checks that are already known before retaining the
            -- sort bucket. The search checks new rules again as it runs.
            eligible t =
                not (t `HS.member` seen s)
                    && either (const False) (sameUpToCarriers tc) (termType inst_sig t)
                    && not (reducible (isGivenVar inst_sig) (rewrite_rules s) (mostGeneral (isGivenVar inst_sig) schema_vars t))
        -- We want to display a message once the first term is found.
        -- in particular, it hangs after this messages for HugeLists 6
        refreshCount progress "Finding first term " (" for " ++ show tc) "" lvl (so_far s)
        first <- diagnose env lvl (show tc) "candidate_list_demand" s $ evaluate terms
        case first of
            (_ : _) -> refreshCount progress "Folded, exploring " (" for " ++ show tc) "" lvl (so_far s)
            _ -> return ()
        let deadline = (\seconds -> bucketStart + round (seconds * 1e9)) <$> bucketTimeout
        memory <- case bucketMemLimit of
            Just bytes -> (\live -> Just (live, bytes)) <$> liveBytes
            Nothing -> return Nothing
        considerAll (deadline, memory, bucketStart, s) lvl tc first s
    considerAll _ _ _ [] s = return ([], s)
    considerAll limit@(deadline, memory, bucketStart, start) lvl tc (t : ts) s = do
        begin <- getMonotonicTimeNSec
        schemaSink <- newIORef []
        let considerOne =
                diagnose env lvl (show tc) "schema" s $
                    consider env{lawSink = schemaSink} stecta lvl (Term "filter" [typeSkeletonToTerm tc, t]) s
        result <- withMemoryLimit memory $ case deadline of
            Nothing -> Just <$> considerOne
            Just d
                | begin >= d -> return Nothing
                | otherwise -> timeout (fromIntegral ((d - begin) `div` 1000)) considerOne
        let stopped reason = do
                -- The bucket ran out of time or memory: keep the laws that the
                -- schema found, drop the rest of the schema, and report.
                found <- reverse <$> readIORef schemaSink
                (kept, s1) <-
                    if parallelBuckets
                        then return ([], s{pending_laws = reverse found ++ pending_laws s})
                        else foldM replay ([], s) found
                now <- getMonotonicTimeNSec
                let tree = Map.findWithDefault DT.empty (typeSkeletonToTerm tc) (trees s)
                putStrLn $
                    reason
                        ++ ": phase "
                        ++ show diagnosticPhase
                        ++ ", size "
                        ++ show lvl
                        ++ ", type "
                        ++ show tc
                        ++ ", after "
                        ++ show (fromIntegral (now - bucketStart) / 1e9 :: Double)
                        ++ " s: "
                        ++ show (so_far s - so_far start)
                        ++ " schemas tested, "
                        ++ show (law_count s - law_count start)
                        ++ " laws, "
                        ++ show (DT.size tree)
                        ++ " representatives; interrupted at "
                        ++ ppNpTerm t
                diagnosticEvent env "stopped" lvl (show tc) "bucket" s1
                return (kept, s1)
        case result of
            Left grown ->
                stopped
                    ("Bucket memory limit (live heap grew by " ++ show (grown `div` (1024 * 1024)) ++ " MiB)")
            Right Nothing -> stopped "Bucket timeout"
            Right (Just (laws, s')) -> considerRest limit lvl tc t ts begin s s' laws
    considerRest limit lvl tc t ts begin s s' laws = do
        end <- getMonotonicTimeNSec
        -- Without parallel buckets, deferred laws print when their schema ends.
        when (deferLaws && not parallelBuckets) $ mapM_ putStrLn laws
        when (isJust onlyBucket && stopAfter == Just (diagnosticPhase, lvl)) $
            hPutStrLn
                stderr
                ( intercalate
                    "\t"
                    [ "schematime"
                    , show (fromIntegral (end - begin) / 1e9 :: Double)
                    , show (length laws)
                    , show (so_far s' - so_far s)
                    , ppNpTerm t
                    ]
                )
        next <- diagnose env lvl (show tc) "candidate_list_demand" s' $ evaluate ts
        (more, s'') <- considerAll limit lvl tc next (if parallelBuckets then s' else s'{pending_laws = []})
        return (laws ++ more, s'')

-- 2. The candidate terms.

-- | The reduced automaton of the terms of a size and a type, with merged type alternatives (see 'mergeTypeAlternatives').
searchSpace :: StEcta -> Int -> TypeSkeleton -> Node Symbol
searchSpace StEcta{..} lvl tc =
    let !ecta = filterType (union $ tk any_arg lvl) $ typeToFta tc
     in mergeTypeAlternatives (fixWithin 100 (withoutRedundantEdges . reducePartially) ecta)

{- | 'Compile.preparePruning', and then 'mergeTypeAlternatives' again,
because its reduction can make overlapping type alternatives.
-}
preparePruning :: [Template Symbol] -> Node Symbol -> (Node Symbol, [Template Symbol])
preparePruning templates = Bi.first mergeTypeAlternatives . Compile.preparePruning templates

-- | 'searchSpace' in disjoint parts, one for each shape of the left spine (see 'spineParts').
searchSpaceParts :: Int -> StEcta -> Int -> TypeSkeleton -> [Node Symbol]
searchSpaceParts splitDepth StEcta{..} lvl tc =
    [ mergeTypeAlternatives (fixWithin 100 (withoutRedundantEdges . reducePartially) (filterType part (typeToFta tc)))
    | part <- spineParts splitDepth any_arg lvl
    ]

{- | Run each action in its own thread, and give the results in order. An
exception in a thread is raised again here.
-}
concurrently :: [IO a] -> IO [a]
concurrently actions = do
    results <- mapM start actions
    mapM (\result -> takeMVar result >>= either (\e -> throwIO (e :: SomeException)) pure) results
  where
    start action = do
        result <- newEmptyMVar
        _ <- forkIO (try action >>= putMVar result)
        pure result

{- | Evaluate the spine of each list in its own thread. With 'True', print the
time and the length of each on stderr. An exception in a thread is raised
again here.
-}
forceInParallel :: Bool -> Int -> TypeSkeleton -> [[a]] -> IO [[a]]
forceInParallel report lvl tc lists = do
    results <- mapM start lists
    timings <- mapM (\result -> takeMVar result >>= either (\e -> throwIO (e :: SomeException)) pure) results
    when report $
        mapM_
            ( \(index, (seconds, n)) -> hPutStrLn stderr (intercalate "\t" ["parpart", show lvl, show tc, show index, show seconds, show n])
            )
            (zip [0 :: Int ..] timings)
    pure lists
  where
    start xs = do
        result <- newEmptyMVar
        _ <- forkIO $ do
            begin <- getMonotonicTimeNSec
            outcome <- try (evaluate (length xs))
            end <- getMonotonicTimeNSec
            putMVar result ((\n -> (fromIntegral (end - begin) / 1e9 :: Double, n)) <$> outcome)
        pure result

{- | Evaluate the spines of the parts of each group in background threads,
and give for each group an action that waits for its parts, and its parts
joined in their order. The threads take the parts in order: the parts of
the first group, then those of the second group, and so on. With more than
one capability, one thread runs on each capability other than the first, so
that the thread that tests keeps its own. A part that fails is left to the
thread that reads it.
-}
enumerateInBackground :: [[[a]]] -> IO [(IO (), [a])]
enumerateInBackground groups = do
    capabilities <- getNumCapabilities
    tagged <- mapM (mapM (\xs -> (,) xs <$> newEmptyMVar)) groups
    queue <- newIORef (concat tagged)
    let worker = do
            next <- atomicModifyIORef' queue (\parts -> case parts of [] -> ([], Nothing); part : rest -> (rest, Just part))
            case next of
                Nothing -> pure ()
                Just (xs, done) -> do
                    _ <- try (evaluate (length xs)) :: IO (Either SomeException Int)
                    putMVar done ()
                    worker
    if capabilities > 1
        then mapM_ (`forkOn` worker) [1 .. capabilities - 1]
        else void (forkIO worker)
    pure [(mapM_ (readMVar . snd) parts, concatMap fst parts) | parts <- tagged]

-- 3. The test of a candidate, and the laws that it gives.

{- | The result of the exploration of a term in the tree of the instances of
a schema, as in QuickSpec.
-}
data Explored
    = -- | The term is a new representative.
      Singleton
    | -- | The term equals a representative: the law.
      Discovered String
    | {- | A known law rewrites the term, the term is a representative already,
      or a comparison threw.
      -}
      Knew

{- | Consider one candidate term. The term is a schema: it has one variable
of each type, which stands for the holes. The rule is that of QuickSpec 2
(section 3.2.3 of the paper, and Explore/Schemas.hs). Prune the schema if a
known law rewrites its most general instance. Otherwise, test the schema
against the representative schemas of its type. If the schema equals a
representative, test its most general instance against the instances of
the representative. If that instance is new, test all instances of the
two schemas. A new representative schema is also instantiated if it is
small. Give the laws that the tests find.
-}
consider :: Settings -> StEcta -> Int -> Term -> Search -> IO ([String], Search)
consider env@Settings{..} StEcta{..} lvl full_term s0
    -- A known law rewrites the most general instance to a smaller term. The
    -- law rewrites each instance in the same way, so the schema is
    -- redundant.
    | reducible isVar (rewrite_rules s0) most_general = return ([], s0)
    -- if we've seen it before, we can immediately skip.
    | np_term `HS.member` seen s0 = return ([], s0{so_far = so_far s0 + 1})
    -- An application of the schema does not fit its argument, or its
    -- equality does not fit its values, so the search does not test it.
    | not (testable np_term) = return ([], s0{so_far = so_far s0 + 1})
    | otherwise = do
        let tree = Map.findWithDefault DT.empty current_ty (trees s0)
            known a b = a == b || joinable isVar (rewrite_rules s0) a b
        refreshCount
            progress
            ("exploring " ++ show current_ty)
            ""
            ("(" ++ show (DT.size tree) ++ " representatives...)")
            lvl
            (so_far s0)
        -- The schema goes into the decision tree of its type. It is
        -- evaluated on the test cases of its path only.
        inserted <-
            diagnose env lvl (show current_ty) "schema_tests" s0 $
                DT.insertWith known (valuesEqual eq_inst) test_cases np_term (values np_term) tree
        let s = s0{so_far = so_far s0 + 1}
            -- A later phase enumerates the schema again, so it goes into
            -- seen.
            s' = s{seen = HS.insert np_term (seen s0)}
        (laws, s'') <- case inserted of
            -- A comparison threw, so the schema does not become a
            -- representative.
            DT.Untested -> return ([], s)
            DT.Distinct tree'
                | lvl <= maxCommutativeSize -> instantiateRep np_term with_tree
                | otherwise ->
                    return
                        ( []
                        , with_tree
                            { instance_trees =
                                Map.insert
                                    np_term
                                    (DT.leafWith most_general (values most_general))
                                    (instance_trees s0)
                            , touched_reps = HS.insert np_term (touched_reps s0)
                            }
                        )
              where
                with_tree = s'{trees = Map.insert current_ty tree' (trees s0)}
            DT.EqualTo rep -> exploreIn rep s'
        refreshCount progress ("exploring " ++ show current_ty) "" "" lvl (so_far s)
        return (laws, s'')
  where -- wrt variable renaming
    np_term = npTerm' full_term
    Term "filter" [current_ty, _] = full_term
    isVar = isGivenVar inst_sig
    most_general = mostGeneral isVar schema_vars np_term

    -- The equality of a type compares the values of that type.
    term_eq_insts = Map.fromList [(typeSkeletonToTerm t, (txt, eq, t)) | (t, (txt, eq)) <- Map.assocs eq_insts]
    (eq_txt, eq_inst, eq_type) = term_eq_insts Map.! current_ty
    -- Whether the tests of a term can run: its applications fit their
    -- arguments, and its equality fits its values, as an application
    -- does (see 'termType').
    testable t = either (const False) (sameUpToCarriers eq_type) (termType inst_sig t)
    -- A function bucket compares its functions on the value of the sample
    -- variable in each test case (see 'function_samples').
    sample = Map.lookup eq_type function_samples
    observe evaluateTerm = case sample of
        Nothing -> evaluateTerm
        Just x -> \vals -> apply (evaluateTerm vals) (vals Map.! x)
    -- The values of a term on the test cases, evaluated when needed.
    values u = case compileTerm inst_sig u of
        Left message -> error message
        Right evaluateTerm ->
            let variables = [v | Symbol v <- holes isVar u] ++ maybeToList sample
                required = Map.fromList [(v, inst_sig Map.! v) | v <- variables]
                evaluateValues
                    | Map.null required = const (evaluateTerm Map.empty)
                    | otherwise = observe evaluateTerm
             in DT.Evaluator required evaluateValues

    -- The schema equals the representative schema rep. Test the most
    -- general instance of the schema against the instances of rep.
    exploreIn rep s = do
        (explored, s') <- diagnose env lvl (show current_ty) "instance" s $ exploreInstance rep most_general s
        case explored of
            Discovered law -> return ([law], s')
            Knew -> return ([], s')
            Singleton -> do
                (rep_laws, s'') <-
                    if rep `HS.member` instantiated s'
                        then return ([], s')
                        else instantiateRep rep s'
                (laws, s''') <- instantiate rep np_term s''
                return (rep_laws ++ laws, s''')

    instantiateRep rep s = instantiate rep rep s{instantiated = HS.insert rep (instantiated s)}

    -- Test the instances of a schema against the instances of the
    -- representative schema rep, the most general instances first.
    instantiate rep schema initial = diagnose env lvl (show current_ty) "instances" initial $ go (schemaInstances isVar schema_vars schema) initial
      where
        go [] s = return ([], s)
        go (i : is) s = do
            (explored, s') <- diagnose env lvl (show current_ty) "instance" s $ exploreInstance rep i s
            (laws, s'') <- go is s'
            return
                ( case explored of
                    Discovered law -> law : laws
                    _ -> laws
                , s''
                )

    -- Test an instance against the instances of the representative
    -- schema rep. Print the law that the test finds, and add its rules.
    exploreInstance rep i s
        | reducible isVar (rewrite_rules s) i = return (Knew, s)
        | not (testable i) = return (Knew, s)
        | otherwise = do
            let table = Map.findWithDefault DT.empty rep (instance_trees s)
                known a b = a == b || joinable isVar (rewrite_rules s) a b
            inserted <-
                diagnose env lvl (show current_ty) "instance_tests" s $
                    DT.insertWith known (valuesEqual eq_inst) test_cases i (values i) table
            case inserted of
                DT.Untested -> return (Knew, s)
                DT.Distinct table' ->
                    return
                        (Singleton, s{instance_trees = Map.insert rep table' (instance_trees s), touched_reps = HS.insert rep (touched_reps s)})
                DT.EqualTo w
                    | w == i -> return (Knew, s)
                    -- The known laws prove the law.
                    | joinable isVar (rewrite_rules s) w i -> do
                        when progress $
                            hPutStrLn stderr ("\r\ESC[Kfollows from the laws: " ++ ppNpTerm (lawOf w))
                        return (Knew, s)
                    | otherwise -> do
                        refuting <- refutingCase w recheck_cases
                        case refuting of
                            Just c -> do
                                hPutStrLn
                                    stderr
                                    ( "*** A small test case refutes a law, which the search drops: "
                                        ++ ppNpTerm (lawOf w)
                                        ++ " ("
                                        ++ show (caseTest c)
                                        ++ ")"
                                    )
                                return (Knew, s)
                            Nothing -> discover w
      where
        lawOf w = Term "(==)" [Term (Symbol eq_txt) [], w, i]
        -- The first extra test case on which the instance and w differ. Each
        -- side is compiled once.
        refutingCase w cases = case (compileTerm inst_sig w, compileTerm inst_sig i) of
            (Right left, Right right) -> firstRefuting (observe left) (observe right) cases
            _ -> return Nothing
        firstRefuting _ _ [] = return Nothing
        firstRefuting left right (c : cs) = do
            equal <- valuesEqual eq_inst (left (caseValues c)) (right (caseValues c))
            if equal == Just False then return (Just c) else firstRefuting left right cs
        discover w = do
            (lawSig, law) <-
                generalizeLaw
                    resolveInstance
                    (map caseTest test_cases)
                    inst_sig
                    ((\x -> (x, inst_sig Map.! x)) <$> sample)
                    (eq_type, eq_inst)
                    (lawOf w)
            let n = law_count s + 1
                law_str = show n <> ". " <> ppNpTerm (canonicalLaw lawSig law)
            unless deferLaws $ do
                when progress $ hPutStr stderr "\r\ESC[K"
                putStrLn law_str
            when dumpLaws $
                hPutStrLn stderr ("specftacular-law\t" ++ show n ++ "\t" ++ show (canonicalLaw lawSig law))
            when deferLaws $ modifyIORef' lawSink ((w, i, lawSig, law) :)
            -- With parallel buckets, the merge completes the law, so the
            -- bucket adds the rules of the law alone.
            let complete
                    | parallelBuckets = return (addLawRules lawSig law (rewrite_rules s))
                    | otherwise =
                        boundedCompletion env law_str (addLaw maxSize lawSig law (rewrite_rules s)) (addLawRules lawSig law (rewrite_rules s))
            rules <-
                if detailedDiagnostics
                    then diagnose env lvl (show current_ty) "completion" s complete
                    else complete
            return
                ( Discovered law_str
                , s
                    { law_count = n
                    , rewrite_rules = rules
                    , pending_laws = [(w, i, lawSig, law) | deferLaws] ++ pending_laws s
                    }
                )

{- | The default number of bytes by which the completion of one law may grow
the live heap (@--completion-mem-limit@). See 'boundedCompletion'. This
limit keeps the machine safe.
-}
completionMemoryLimit :: Word64
completionMemoryLimit = 4 * 1024 * 1024 * 1024

{- | The default number of bytes that the completion of one law may allocate
(@--completion-alloc-limit@). See 'boundedCompletion'. This limit stops a
completion that runs long within the memory limit: at 6-p4, one completion
runs more than 25 minutes within 4 GiB of live heap. The most expensive
completion of HugeLists 7-p3 up to phase 3 size 5 that ends allocates
184 GiB. A law that keeps only its own rules can make the completions of the
laws after it expensive too, so the budget is above the costs of the
completions that end.
-}
completionBudget :: Word64
completionBudget = 256 * 1024 * 1024 * 1024

{- | The completed rules of a law, if their computation stays within the
limits of the completion (see 'completionTimeout', 'completionMemLimit',
'completionAllocLimit'), and else the rules of the law alone, with a report
on stderr. Completion only adds rules that follow from the laws, so fewer
rules prune less but stay sound. The allocation does not depend on the load.
The time does, and the memory limit depends on the times of the collections.
Without RTS statistics (@+RTS -T@) there is no memory limit.
-}
boundedCompletion :: Settings -> String -> Rules -> Rules -> IO Rules
boundedCompletion Settings{..} label completed alone = do
    statsEnabled <- getRTSStatsEnabled
    base <- if statsEnabled then Just <$> liveBytes else pure Nothing
    begin <- getMonotonicTimeNSec
    setAllocationCounter (fromIntegral completionAllocLimit)
    enableAllocationLimit
    result <-
        try $
            withMemoryLimit ((\live -> (live, completionMemLimit)) <$> base) $
                case completionTimeout of
                    Nothing -> Just <$> evaluate completed
                    Just seconds -> timeout (round (seconds * 1e6)) (evaluate completed)
    disableAllocationLimit
    left <- getAllocationCounter
    end <- getMonotonicTimeNSec
    -- A completion that allocates more than 1 GiB prints its cost on stderr.
    let allocated = fromIntegral completionAllocLimit - fromIntegral left :: Double
    when (allocated > 1024 ^ (3 :: Int)) $
        hPutStrLn
            stderr
            ( intercalate
                "\t"
                ["completioncost", show (fromIntegral (end - begin) / 1e9 :: Double), show (allocated / 1024 ^ (3 :: Int)), label]
            )
    case result of
        Right (Right (Just rules)) -> return rules
        Right (Right Nothing) -> do
            hPutStrLn stderr ("completion over its time limit, the law alone: " ++ label)
            return alone
        Right (Left grown) -> do
            hPutStrLn
                stderr
                ( "completion over its memory limit (live heap grew by "
                    ++ show (grown `div` (1024 * 1024))
                    ++ " MiB), the law alone: "
                    ++ label
                )
            return alone
        Left AllocationLimitExceeded -> do
            hPutStrLn stderr ("completion over its budget, the law alone: " ++ label)
            return alone

npTerm' :: Term -> Term
npTerm' (Term "filter" [_, term]) = npTerm' term
npTerm' (Term "app" [t, _, a, v]) = (Term "app" $ [t, npTerm' a, npTerm' v])
npTerm' t = t

ppNpTerm :: Term -> String
ppNpTerm t
    | (Term "(==)" [_, lhs, rhs]) <- t = ppTerm' False lhs <> " == " <> ppTerm' False rhs
    | otherwise = ppTerm' False t
  where
    ppTerm' True (Term "app" [_, f, v]) = "(" <> ppTerm' True f <> " " <> ppTerm' True v <> ")"
    ppTerm' _ (Term "app" [_, f, v]) = ppTerm' True f <> " " <> ppTerm' True v
    ppTerm' True (Term "app" [f, v]) = "(" <> ppTerm' True f <> " " <> ppTerm' True v <> ")"
    ppTerm' _ (Term "app" [f, v]) = ppTerm' True f <> " " <> ppTerm' True v
    ppTerm' True (Term (Symbol t) _) = parIfReq (T.unpack t)
    ppTerm' _ (Term (Symbol t) _) = T.unpack t
    parIfReq s@(c : _) | c /= '(', c /= '[', not (isAlphaNum c) = "(" <> s <> ")"
    parIfReq s = s

{- | Show the progress of the search on one line of stderr, if the first
argument is True.
-}
refreshCount :: Bool -> String -> String -> String -> Int -> Int -> IO ()
refreshCount False _ _ _ _ _ = return ()
refreshCount True pre mid post size i = hPutStr stderr (o ++ fill ++ "\r") >> hFlush stderr
  where
    o' =
        "\r\ESC[K"
            ++ pre
            ++ " terms of size "
            ++ show size
            ++ mid
            ++ ", "
            ++ show i
            ++ " examined so far. "
    o =
        if length (o' ++ post) <= 120
            then o' ++ post
            else (take 117 (o' ++ post)) ++ "..."
    fill = replicate (max 0 (length o - 120)) ' '

-- TODO:
-- 2. knuth-bendix completion algorithm (we're almost there)
--    what to do when the size is the same? We want only one way to reduce a term
--    resolve critical pairs: if a term can be rewritten with two different rules
--    might not be stable, but we *don't need confluence*. Term indexing:
--    have a hashtable of the root node. Makes it a lot faster.
-- 11. make term a pattern synonym and compute the hash when we construct
--     the term.
--
-- Check for equality in the presence of non-total functions, e.g.
-- reverse (reverse xs) = xs. Allow an option to add more information for this,
-- i.e. reverse (reverse xs) = traverse xs, but not xs.
-- functions should also behave the same on the undefined list.
--
-- i.e. False && a = False
-- but  a && False = seq a False
--
--
