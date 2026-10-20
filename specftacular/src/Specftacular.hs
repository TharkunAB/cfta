{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Specftacular (
    module Specftacular.Types,
    module Data.Proxy,
    ftacularSpec,
    discoverMonomorphic,
    experimentalPhases,
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

import Control.Exception (AllocationLimitExceeded (..), evaluate, mask, onException, try)
import Control.Monad (when)
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
import Data.Int (Int64)
import Data.List hiding (union)
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import qualified Data.Text as T
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Conc (disableAllocationLimit, enableAllocationLimit, setAllocationCounter)
import GHC.Stats (RTSStats (allocated_bytes, gc_cpu_ns, gcs), getRTSStats, getRTSStatsEnabled)
import System.CPUTime (getCPUTime)
import qualified System.Environment as Env
import qualified Text.Read as TR

import Data.Containers.ListUtils (nubOrd)
import qualified Data.HashSet as HS
import System.IO (hFlush, hPutStr, hPutStrLn, stderr)

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
    , schema_vars :: Map Symbol [Symbol]
    {- ^ The variables of each type, from the variable with
    the index 0 of the type.
    -}
    , test_cases :: [Case]
    -- ^ The test cases that all terms of the phase share, with the values of the variables.
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
    }

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
discoverMonomorphic size = experimentalPhases size 1

{- | The laws of a signature, with the phases from 1 to the given phase.
Phases 2 to 4 are experimental. Phase 2 keeps A, B, C, D, and Acc apart.
Phases 3 and 4 instantiate the abstract carrier types of each constant.
The search checks every instance before evaluation (see 'termType').
-}
experimentalPhases :: Int -> Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> [Sig] -> IO [String]
experimentalPhases size phase extraReps sigs = searchPhases size phase (frontInstances extraReps) (mconcat sigs)

{- | 'experimentalPhases' with the instances of the types for the search,
for a front end that does not give the types of the values to Haskell,
such as a GHC session.
-}
searchPhases :: Int -> Int -> (TypeSkeleton -> Maybe Instance) -> Sig -> IO [String]
searchPhases size phase givenInstances givenSig =
    do
        -- SPECFTACULAR_PROGRESS=1 shows the progress of the search on stderr.
        progress <- (== Just "1") <$> Env.lookupEnv "SPECFTACULAR_PROGRESS"
        diagnosticSetting <- Env.lookupEnv "SPECFTACULAR_DIAGNOSTICS"
        let diagnostics = diagnosticSetting `elem` [Just "1", Just "phases"]
            detailedDiagnostics = diagnosticSetting == Just "1"
        -- SPECFTACULAR_TESTS sets the number of test cases (1000 by default,
        -- as in QuickSpec).
        numTests <- fromMaybe 1000 . (>>= TR.readMaybe) <$> Env.lookupEnv "SPECFTACULAR_TESTS"
        -- SPECFTACULAR_CHECKED=1 keeps the types of the values, and tests
        -- them at each application (see 'Value').
        checked <- (== Just "1") <$> Env.lookupEnv "SPECFTACULAR_CHECKED"
        let sig
                | checked = givenSig
                | otherwise = untypedSig givenSig
            instances
                | checked = givenInstances
                | otherwise = fmap untypedInstance . givenInstances
        let StEcta
                { compl_sig = compl_sig
                , arb_insts = arb_insts
                , sig_ty_cons = sig_ty_cons
                } = mkStecta size numTests instances sig False id id
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
                    }
        runPhases env size (max 1 (min 4 phase)) instances sig

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
    (TypeSkeleton -> Maybe Instance) ->
    Sig ->
    Bool ->
    (TypeSkeleton -> TypeSkeleton) ->
    (TypeSkeleton -> TypeSkeleton) ->
    StEcta
mkStecta size numTests instances sig closed givenTrans skelTrans =
    StEcta
        { any_arg = ag
        , compl_sig = compl_sig
        , given_sig = givenSig
        , phase_variables = Map.fromList [(sfTypeRep f, Symbol name) | (name, f) <- Map.assocs givenSig]
        , inst_sig = inst_sig
        , schema_vars = Map.fromList [(Symbol x, map (Symbol . fst) vs) | (x, vs) <- moreVars]
        , sig_ty_cons = Map.keys eq_insts
        , eq_insts = eq_insts
        , test_cases = withValues inst_sig (testSchedule numTests)
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
    inst_sig = Map.fromList (concatMap snd moreVars) <> compl_sig
    (givenSig, eq_insts, arbs) = sigGivens closed givenTrans sig instances
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
    gnodes = addSyms id (generalize sc)

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
            }
  where
    go ((pn, (finished, starting, givenTrans, skelTrans, skeletonTrans)) : rest) s
        | pn <= lastPhase = do
            when (pn > 1) $ putStrLn starting
            let phaseEnv = env{diagnosticPhase = pn}
                -- A phase with a skeleton grammar closes its variable types
                -- under carrier renaming, so each renaming of a typing of a
                -- skeleton has its variables.
                stectaWith variableTrans = mkStecta size (numTests env) instances sig (isJust skeletonTrans) variableTrans skelTrans
            (laws, s') <- diagnose phaseEnv 0 "" "phase" s $ do
                result@(_, finishedState) <- runPhase phaseEnv size (stectaWith <$> skeletonTrans) (stectaWith givenTrans) s
                diagnosticEvent phaseEnv "checkpoint" 0 "" "phase" finishedState
                return result
            putStrLn $ finished ++ show (so_far s') ++ " terms examined."
            putStrLn $ show (sum $ map DT.size $ Map.elems (trees s')) ++ " unique terms discovered."
            (laws ++) <$> go rest s'
    go _ _ = return []

{- | Run one phase: the sizes from 1 to the given size, and for each size
each type to test. With a skeleton grammar, the candidates of a type are the
most general carrier typings with that result type of the skeletons of its
monomorphic type.
-}
runPhase :: Settings -> Int -> Maybe StEcta -> StEcta -> Search -> IO ([String], Search)
runPhase env@Settings{..} size skeletons stecta@StEcta{..} =
    go
        Map.empty
        [(lvl, tc) | lvl <- [1 .. size], tc <- sortOn (\t -> (typeSize t, concreteTypeLeaves t, t)) (filter tested sig_ty_cons)]
  where
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
            cache' = case skeletons of
                Just skeleton
                    | Map.notMember (lvl, key) current -> Map.insert (lvl, key) (skeletonTypings skeleton lvl key (rewrite_rules s)) current
                _ -> current
        (laws, s') <- diagnose env lvl (show tc) "bucket" s $ do
            result@(_, finishedState) <- bucket lvl (Map.lookup (lvl, key) cache') tc s
            diagnosticEvent env "checkpoint" lvl (show tc) "bucket" finishedState
            return result
        (more, s'') <- go cache' rest s'
        return (laws ++ more, s'')
    -- The principal typings of the skeletons of a size and a monomorphic type
    -- (see 'generalizeCarriers'). Only templates without annotations prune a
    -- skeleton, because they match each typing of it.
    skeletonTypings skeleton@StEcta{compl_sig = skeletonSig} lvl monomorphic rules =
        let templates
                | canPrune = filter annotationFree (pruningTemplates skeletonSig lvl rules)
                | otherwise = []
            (pruningRoot, oracleTemplates) = Compile.preparePruning templates (refold (searchSpace skeleton lvl monomorphic))
         in mapMaybe (generalizeCarriers skeletonSig phase_variables . npTerm') (prunedTerms oracleTemplates pruningRoot)
    bucket lvl typings tc s = do
        produced <- case typings of
            Just typingsOfType -> pure $ nubOrd (mapMaybe ($ tc) typingsOfType)
            Nothing -> do
                refreshCount progress "Reducing  ECTA" (" for " ++ show tc) "" lvl (so_far s)
                reduced <- diagnose env lvl (show tc) "reduce_whnf" s $ evaluate (searchSpace stecta lvl tc)
                let templates
                        | canPrune = pruningTemplates compl_sig lvl (rewrite_rules s)
                        | otherwise = []
                refreshCount progress "Refolding ecta" (" for " ++ show tc) "" lvl (so_far s)
                folded <- diagnose env lvl (show tc) "refold_whnf" s $ evaluate (refold reduced)
                -- The oracle rejects partial branches before their remaining type
                -- choices expand. The bucket has one program size. KBO orders its
                -- ties before testing; smaller sizes have already supplied rules.
                let (pruningRoot, oracleTemplates) = Compile.preparePruning templates folded
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
        considerAll lvl tc first s
    considerAll _ _ [] s = return ([], s)
    considerAll lvl tc (t : ts) s = do
        (laws, s') <-
            diagnose env lvl (show tc) "schema" s $ consider env stecta lvl (Term "filter" [typeSkeletonToTerm tc, t]) s
        next <- diagnose env lvl (show tc) "candidate_list_demand" s' $ evaluate ts
        (more, s'') <- considerAll lvl tc next s'
        return (laws ++ more, s'')

-- 2. The candidate terms.

-- | The reduced automaton of the terms of a size and a type.
searchSpace :: StEcta -> Int -> TypeSkeleton -> Node Symbol
searchSpace StEcta{..} lvl tc =
    let !ecta = filterType (union $ tk any_arg lvl) $ typeToFta tc
     in fixWithin 100 (withoutRedundantEdges . reducePartially) ecta

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
    -- The values of a term on the test cases, evaluated when needed.
    values u = case compileTerm inst_sig u of
        Left message -> error message
        Right evaluateTerm ->
            let required = Map.fromList [(v, inst_sig Map.! v) | Symbol v <- holes isVar u]
                evaluateValues
                    | Map.null required = const (evaluateTerm Map.empty)
                    | otherwise = evaluateTerm
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
                    return (Singleton, s{instance_trees = Map.insert rep table' (instance_trees s)})
                DT.EqualTo w
                    | w == i -> return (Knew, s)
                    -- The known laws prove the law.
                    | joinable isVar (rewrite_rules s) w i -> do
                        when progress $
                            hPutStrLn stderr ("\r\ESC[Kfollows from the laws: " ++ ppNpTerm (lawOf w))
                        return (Knew, s)
                    | otherwise -> do
                        (lawSig, law) <- generalizeLaw resolveInstance (map caseTest test_cases) inst_sig (eq_type, eq_inst) (lawOf w)
                        let n = law_count s + 1
                            law_str = show n <> ". " <> ppNpTerm (canonicalLaw lawSig law)
                        when progress $ hPutStr stderr "\r\ESC[K"
                        putStrLn law_str
                        let complete = boundedCompletion law_str (addLaw maxSize lawSig law (rewrite_rules s)) (addLawRules lawSig law (rewrite_rules s))
                        rules <-
                            if detailedDiagnostics
                                then diagnose env lvl (show current_ty) "completion" s complete
                                else complete
                        return
                            ( Discovered law_str
                            , s
                                { law_count = n
                                , rewrite_rules = rules
                                }
                            )
      where
        lawOf w = Term "(==)" [Term (Symbol eq_txt) [], w, i]

{- | The number of bytes that the completion of one law may allocate. See
'boundedCompletion'.
-}
completionBudget :: Int64
completionBudget = 64 * 1024 * 1024 * 1024

{- | The completed rules of a law, if their computation allocates at most
'completionBudget' bytes, and else the rules of the law alone, with a report
on stderr. Completion only adds rules that follow from the laws, so fewer
rules prune less but stay sound. The allocation does not depend on the load,
so the choice is the same in each run.
-}
boundedCompletion :: String -> Rules -> Rules -> IO Rules
boundedCompletion label completed alone = do
    setAllocationCounter completionBudget
    enableAllocationLimit
    result <- try (evaluate completed)
    disableAllocationLimit
    case result of
        Right rules -> return rules
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
