{-# LANGUAGE OverloadedStrings #-}

{- | Fits for a hole: Hectare proposes programs, and a walk inside GHC's
typechecker checks them.

The entry point runs inside an existing 'TcM' context, as GHC's hole-fit
machinery does, so that a hole-fit plugin can call it. It takes GHC's
'TypedHole', the 'Candidate's of the hole's scope, and the goal type, as
'GHC.Tc.Errors.Hole.tcCheckHoleFit' does:

* Hectare's equality-constrained automaton ("Data.CFTA.Gen.Synthesis")
  lists the programs of each size over the candidates' erased types
  ("Data.CFTA.GHC.Erase"), smallest first, in its enumeration order. A
  candidate with a higher-kinded type variable, as @fmap@ or @(>>=)@, has
  an erased type at each type head of the query whose class constraints GHC
  solves under the hole's givens ('specializations').
* Each program is checked in preorder, one leaf at a time
  ("Data.CFTA.GHC.Internal.Check"), as a refinement hole fit, with the
  parts of 'GHC.Tc.Errors.Hole.tcCheckHoleFit': 'tcSubTypeSigma' at the
  level of the innermost implication, the fast path for obviously insoluble
  equalities, and the solver with early abort inside the hole's
  implications.
* The walk keeps the checked prefix of the last program. The next program
  backtracks to the longest prefix that it shares with the last one, by a
  restore of the frozen unification variables, and checks only the rest. A
  prefix that fails goes into a trie of dead prefixes, so every later
  program under it is skipped without a step.
* The verdict of a step depends only on the walker's state, up to the names
  of its unification variables, and on the leaf ('StateKey'). The walk keeps
  the verdicts in a table: a step that failed before from the same state is
  skipped without a check, and a step that passed before does not call the
  solver.
* The walk stops after the first fits, after a size, after a number of
  programs, or at a deadline.
* The figures of a search give the time of each part: Hectare's
  construction, reduction, and listing, and the checks in the
  typechecker.
* Each fit tells whether it ignores part of itself, by an exact check in
  GHC's terms: by parametricity, a program cannot use a subterm when it
  still fits with a value of a fresh rigid type in the place of that
  subterm. Such a fit, as @const xs n@ or @const (length xs) p@, has a
  smaller program that does the same.

Why these types:

* The hole is GHC's own 'TypedHole': a plugin's 'GHC.Tc.Errors.Hole.Plugin.FitPlugin'
  gets one, and its implications (with the skolems, the givens, and the
  level) and its relevant constraints are what the check needs. A driver
  without a typechecked hole (the benchmark, with a skolemised signature)
  makes one with 'holeFor'.
* A 'Candidate' is a name with a type, not an 'GHC.Types.Id.Id': a query
  argument of the benchmark has a skolem type and no 'GHC.Types.Id.Id',
  built-in syntax as @(:)@ reaches a plugin as a name, and the text of a fit
  (qualified or not) depends on how the caller sees the scope.
  'candidateFromId' covers the common case.
* The core, 'streamFits', calls a function on each fit and stops when it
  says so, so that a caller can stop at a known program, as the benchmark
  does. 'synthesizeFits' keeps the first fits.
-}
module Data.CFTA.GHC.Fits (
    -- * Holes
    TypedHole (..),
    holeFor,
    Candidate (..),
    candidateFromId,

    -- * Options
    Options (..),
    defaultOptions,
    hectareAvoid,

    -- * Fits
    Fit (..),
    Statistics (..),
    synthesizeFits,
    streamFits,
) where

import Control.Applicative ((<|>))
import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import System.Timeout (timeout)

import Data.CFTA.GHC.Erase (anyResult, erase, higherKinded, typeHeads)
import Data.CFTA.GHC.Internal.Check
import Data.CFTA.Gen.Synthesis (Program (..), Query (..), expand, library, programsIn, rawSearchSpace, reduceFully)
import Data.CFTA.Interned (refold)
import GHC.Builtin.Types (listTyCon)
import GHC.Core.DataCon (dataConNonlinearType)
import GHC.Core.TyCo.FVs (tyCoVarsOfType, tyCoVarsOfTypesList)
import GHC.Core.Type (Type, substTyWith, tyConAppTyCon_maybe)
import GHC.Data.Bag (bagToList, emptyBag)
import GHC.Tc.Errors.Hole.FitTypes (TypedHole (..))
import GHC.Tc.Types.Constraint (Implication (..), ctEvPred)
import GHC.Tc.Types.Origin (SkolemInfoAnon (RuntimeUnkSkol))
import GHC.Tc.Utils.Monad (TcM)
import GHC.Tc.Utils.TcMType (newImplication, newTcEvBinds)
import GHC.Tc.Utils.TcType (TcLevel, TcTyVar, mkSpecSigmaTy, tcSplitNestedSigmaTys)
import GHC.Types.Id (Id, idType, isDataConWorkId_maybe, isDataConWrapId_maybe)
import GHC.Types.Name (getOccString)
import GHC.Types.Var (EvVar, isTyVar)
import GHC.Types.Var.Set (elemVarSet)

{- | A hole under one implication with the given skolems and givens, at the
given level (the skolems' level): what a driver without a typechecked hole
needs, for example after 'GHC.Tc.Utils.Instantiate.topSkolemise' of a
signature. The hole has no relevant constraints.
-}
holeFor :: TcLevel -> [TcTyVar] -> [EvVar] -> TcM TypedHole
holeFor level skolems givens = do
    implication <- newImplication
    binds <- newTcEvBinds
    pure
        TypedHole
            { th_relevant_cts = emptyBag
            , th_implics =
                [ implication
                    { ic_tclvl = level
                    , ic_skols = skolems
                    , ic_given = givens
                    , ic_info = RuntimeUnkSkol
                    , ic_binds = binds
                    }
                ]
            , th_hole = Nothing
            }

{- | A candidate for a fit: its text in a program, its type, whether it can
head an application, and whether every fit must use it. A closed type is
instantiated at each use; a type with free type variables keeps them.
-}
data Candidate = Candidate
    { candidateName :: Text
    , candidateType :: Type
    , candidateHeads :: Bool
    , candidateRequired :: Bool
    }

{- | An identifier as a candidate with the given text, which can head an
application and is not required. A data constructor's arrows are linear in
its identifier's type (@a %1 -> [a] %1 -> [a]@), so its candidate has the
type with unrestricted arrows, 'dataConNonlinearType', as GHC's own hole
fits use.
-}
candidateFromId :: Text -> Id -> Candidate
candidateFromId name identifier = Candidate name typ True False
  where
    typ =
        maybe (idType identifier) dataConNonlinearType (isDataConWrapId_maybe identifier <|> isDataConWorkId_maybe identifier)

-- | The options of a search.
data Options = Options
    { optionMaximumSize :: Int
    -- ^ The largest program, in leaves.
    , optionFits :: Int
    -- ^ For 'synthesizeFits': the number of fits to stop after.
    , optionMaximumPrograms :: Maybe Int
    -- ^ The number of Hectare's programs to stop after.
    , optionSeconds :: Maybe Double
    {- ^ The seconds to stop after. The search stops between two checks, or
    stops the construction or the reduction of an automaton.
    -}
    , optionAvoid :: [([Text], Maybe [Text])]
    {- ^ Hectare's pruning rules for programs of size two: a candidate of the
    first list is not applied to one of the second list (with 'Nothing': to
    any), as Hectare does for @head []@.
    -}
    , optionReport :: Maybe (Int -> Statistics -> IO ())
    -- ^ A function to call after each size.
    , optionTrace :: Maybe (Int -> Program -> IO ())
    -- ^ A function to call before each program is checked, with its size.
    }

-- | Programs of up to five leaves, the first ten fits, no other limit.
defaultOptions :: Options
defaultOptions =
    Options
        { optionMaximumSize = 5
        , optionFits = 10
        , optionMaximumPrograms = Nothing
        , optionSeconds = Nothing
        , optionAvoid = []
        , optionReport = Nothing
        , optionTrace = Nothing
        }

{- | Hectare's pruning rule of the Hoogle+ library, with GHC's names, for
'optionAvoid': a list function is not applied to @[]@.
-}
hectareAvoid :: [([Text], Maybe [Text])]
hectareAvoid =
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

-- | A program that fits, with its size in leaves.
data Fit = Fit
    { fitProgram :: Program
    , fitSize :: Int
    , fitIgnoresPart :: Bool
    {- ^ Whether the program still fits when one of its argument subterms
    has a fresh rigid type: then it cannot use that subterm, except with
    'seq'.
    -}
    }
    deriving (Eq, Show)

-- | The figures of a search.
data Statistics = Statistics
    { statisticsPrograms :: !Int
    -- ^ The programs that Hectare proposed.
    , statisticsSkipped :: !Int
    -- ^ The programs under a dead prefix, skipped without a step.
    , statisticsFits :: !Int
    , statisticsSize :: !Int
    -- ^ The size of the last program looked at.
    , statisticsOutOfTime :: !Bool
    -- ^ Whether the search stopped at the deadline.
    , statisticsBuildNanos :: !Word64
    -- ^ The time of Hectare's construction of the automata.
    , statisticsReduceNanos :: !Word64
    -- ^ The time of Hectare's reduction of the automata.
    , statisticsListNanos :: !Word64
    -- ^ The time to list Hectare's programs.
    , statisticsCheckNanos :: !Word64
    -- ^ The time of the checks in the typechecker.
    , statisticsCounters :: !Counters
    }
    deriving (Eq, Show)

{- | The first fits of a hole, as many as 'optionFits'. The search stops
after so many fits that use every part of themselves; a fit that ignores a
part ('fitIgnoresPart') comes after them.
-}
synthesizeFits :: Options -> TypedHole -> [Candidate] -> Type -> TcM [Fit]
synthesizeFits options hole candidates goal = do
    found <- liftIO (newIORef [])
    _ <-
        streamFits options hole candidates goal $ \fit -> do
            fits <- liftIO (modifyIORef' found (fit :) >> readIORef found)
            pure (length (filter (not . fitIgnoresPart) fits) < optionFits options)
    fits <- reverse <$> liftIO (readIORef found)
    pure (take (optionFits options) (filter (not . fitIgnoresPart) fits <> filter fitIgnoresPart fits))

{- | Check Hectare's programs for a hole in its enumeration order, and call
the function on each fit; stop when it returns 'False'. The result has the
figures of the search.
-}
streamFits :: Options -> TypedHole -> [Candidate] -> Type -> (Fit -> TcM Bool) -> TcM Statistics
streamFits options hole candidates goal accept = do
    environment <- newEnvironment hole
    begin <- liftIO getMonotonicTimeNSec
    let deadline = (\seconds -> begin + round (seconds * 1e9)) <$> optionSeconds options
    erased <- concat <$> mapM (erasures environment) candidates
    let (hectareLibrary, query) = hectare erased
    case query of
        Just hectareQuery -> do
            ignoredLeaf <- rigidLeaf environment ignored
            let start = startWalker environment (map candidateType candidates) goal
            startKey <- stateKey environment (walkerVariables start) start
            walk environment hectareLibrary start startKey (Map.insert ignored ignoredLeaf leaves) hectareQuery deadline
        Nothing -> statisticsOf emptySearch <$> readCounters environment
  where
    -- Hectare's automaton has symbols of its own, as app and filter, so each
    -- name gets a prefix there. The k-th specialization of a candidate has
    -- the number after a space, which no Haskell name has.
    prefix = ("ghc:" <>)
    unprefix program = case program of
        Var name -> Var (Text.takeWhile (/= ' ') (fromMaybe name (Text.stripPrefix "ghc:" name)))
        App function argument -> App (unprefix function) (unprefix argument)
    -- The free type variables of the scope, named in order of occurrence.
    relevant = map ctEvPred (bagToList (th_relevant_cts hole))
    free = nub (filter isTyVar (tyCoVarsOfTypesList (goal : relevant <> map candidateType candidates)))
    names =
        Map.fromList
            [ (variable, "@" <> Text.pack (getOccString variable) <> Text.pack (show index))
            | (index, variable) <- zip [0 :: Int ..] free
            ]
    rigid variable = Map.lookup variable names
    -- The Hectare types of a candidate, each with its name in Hectare: its
    -- erased type, or else its specializations at the type heads of the
    -- query.
    erasures environment candidate = case erase rigid (candidateType candidate) of
        Just typ -> pure [(candidate, prefix (candidateName candidate), typ) | keep candidate typ]
        Nothing -> do
            specialized <- specializations environment queryHeads (candidateType candidate)
            pure
                [ (candidate, prefix (candidateName candidate) <> " " <> Text.pack (show index), typ)
                | (index, typ) <- zip [1 :: Int ..] (mapMaybe (erase rigid) specialized)
                , keep candidate typ
                ]
    keep candidate typ = candidateRequired candidate || not (anyResult typ)
    -- The list head is left out: the list functions already cover it (map
    -- for fmap, concatMap for (>>=)), and its specializations would repeat
    -- their fits.
    queryHeads =
        filter
            ((/= Just listTyCon) . tyConAppTyCon_maybe)
            (typeHeads (goal : [candidateType candidate | candidate <- candidates, candidateRequired candidate]))
    hectare erased = (hectareLibrary, query)
      where
        components = [(name, typ) | (candidate, name, typ) <- erased, not (candidateRequired candidate), candidateHeads candidate]
        argumentOnly = [(name, typ) | (candidate, name, typ) <- erased, not (candidateRequired candidate), not (candidateHeads candidate)]
        required = [(name, typ) | (candidate, name, typ) <- erased, candidateRequired candidate]
        hectareLibrary =
            library
                components
                argumentOnly
                [ (concatMap specializedNames heads, concatMap specializedNames <$> arguments)
                | (heads, arguments) <- optionAvoid options
                ]
        -- Hectare's names of the candidates of a name, with their specializations.
        specializedNames text = [name | (candidate, name, _) <- erased, candidateName candidate == text]
        query
            | length required == length (filter candidateRequired candidates) = Query required <$> erase rigid goal
            | otherwise = Nothing
    leaves :: Map Text Leaf
    leaves =
        Map.fromListWith
            (\_ old -> old)
            [(candidateName c, Leaf (candidateName c) (candidateType c) (candidateHeads c)) | c <- candidates]
    -- The name of the rigid leaf: a hole, so no candidate has it.
    ignored = "_"
    walk environment hectareLibrary start startKey leaves' hectareQuery deadline = sizes 1 emptySearch
      where
        -- Build and reduce the automaton of each size, then check its
        -- programs: 'Data.CFTA.Gen.Synthesis.solutionsOfSize' in parts, so
        -- that each part has its own time.
        sizes size search
            | size > optionMaximumSize options = finish search
            | otherwise = do
                (built, buildTime) <- liftIO (timed deadline (rawSearchSpace hectareLibrary hectareQuery size))
                let search' = search{searchSize = size, searchBuild = searchBuild search + buildTime}
                case built of
                    Nothing -> stop search'{searchOutOfTime = True}
                    Just raw -> do
                        (reduced, reduceTime) <- liftIO (timed deadline (refold (reduceFully raw)))
                        let search'' = search'{searchReduce = searchReduce search' + reduceTime}
                        case reduced of
                            Nothing -> stop search''{searchOutOfTime = True}
                            Just space ->
                                programs
                                    size
                                    [program | representative <- programsIn space, program <- expand hectareLibrary representative]
                                    search''
        programs size remaining search
            | maybe False (searchPrograms search >=) (optionMaximumPrograms options) = stop search
            | otherwise = do
                (next, listTime) <- liftIO (timed Nothing (nextProgram remaining))
                let search' = search{searchList = searchList search + listTime}
                case next of
                    Just (Just (program, tokens, rest)) -> do
                        mapM_ (\trace -> liftIO (trace size program)) (optionTrace options)
                        before <- liftIO getMonotonicTimeNSec
                        if maybe False (before >=) deadline
                            then stop search'{searchOutOfTime = True}
                            else do
                                checked <-
                                    check
                                        environment
                                        start
                                        startKey
                                        leaves'
                                        search'{searchPrograms = searchPrograms search' + 1}
                                        size
                                        program
                                        tokens
                                after <- liftIO getMonotonicTimeNSec
                                let search'' = checked{searchCheck = searchCheck checked + (after - before), searchLastFit = Nothing}
                                more <- maybe (pure True) accept (searchLastFit checked)
                                if more then programs size rest search'' else stop search''
                    _ -> report search' >> sizes (size + 1) search'
        -- The next program, with its tokens evaluated, so that the listing
        -- has its own time.
        nextProgram remaining = case remaining of
            [] -> Nothing
            representative : rest ->
                let program = unprefix representative
                    tokens = preorder program
                 in rnf tokens `seq` Just (program, tokens, rest)
        stop search = report search >> finish search
        -- Leave no unification behind: the bottom frame was frozen before
        -- the first step of the last program.
        finish search = do
            case reverse (searchStack search) of
                frame : _ -> restore environment (frameFrozen frame)
                [] -> pure ()
            statisticsOf search <$> readCounters environment
        report search = case optionReport options of
            Just callback -> do
                counters <- readCounters environment
                liftIO (callback (searchSize search) (statisticsOf search counters))
            Nothing -> pure ()
    statisticsOf search =
        Statistics
            (searchPrograms search)
            (searchSkipped search)
            (searchFits search)
            (searchSize search)
            (searchOutOfTime search)
            (searchBuild search)
            (searchReduce search)
            (searchList search)
            (searchCheck search)
    check environment start startKey leaves' search size program tokens
        | isDead tokens (searchDead search) = pure search{searchSkipped = searchSkipped search + 1, searchSize = size}
        | otherwise = do
            let kept = commonPrefix (map frameToken (reverse (searchStack search))) tokens
                stack = drop (length (searchStack search) - kept) (searchStack search)
            -- One restore suffices: the first frame that goes was frozen
            -- before its step, with every variable that existed then.
            case drop kept (reverse (searchStack search)) of
                frame : _ -> restore environment (frameFrozen frame)
                [] -> pure ()
            forward
                environment
                startKey
                leaves'
                search{searchStack = stack, searchSize = size}
                (drop kept tokens)
                kept
                start
                size
                program
    forward environment startKey leaves' search remaining depth start size program = case remaining of
        [] -> do
            let walker = maybe start frameWalker (headMaybe (searchStack search))
                key = maybe startKey frameKey (headMaybe (searchStack search))
            fits <- case Map.lookup (key, endToken) (searchVerdicts search) of
                Just known -> known <$ countKnown environment known
                Nothing -> complete environment walker
            let search' = search{searchVerdicts = Map.insert (key, endToken) fits (searchVerdicts search)}
                -- Two specializations of a candidate can give one program.
                new = Set.notMember (preorder program) (searchReported search)
            if fits && new
                then do
                    -- Undo the program's steps, and check the program with
                    -- each argument subterm in turn of a fresh rigid type.
                    -- The next program starts from the hole.
                    mapM_ (restore environment . frameFrozen) (lastMaybe (searchStack search))
                    ignoresPart <- anyM (fitsFrom environment leaves' start . preorder) (replacements ignored program)
                    pure
                        search'
                            { searchStack = []
                            , searchReported = Set.insert (preorder program) (searchReported search)
                            , searchFits = searchFits search + 1
                            , searchLastFit = Just (Fit program size ignoresPart)
                            }
                else pure search'
        token@(name, children) : rest -> do
            let walker = maybe start frameWalker (headMaybe (searchStack search))
                key = maybe startKey frameKey (headMaybe (searchStack search))
                known = Map.lookup (key, token) (searchVerdicts search)
                dead = take (depth + 1) (map frameToken (reverse (searchStack search)) <> [token])
            case known of
                Just False -> do
                    countKnown environment False
                    pure search{searchDead = markDead dead (searchDead search)}
                _ -> do
                    frozen <- freeze environment walker
                    stepped <- case Map.lookup name leaves' of
                        Just leaf -> step environment walker leaf children (known == Just True)
                        Nothing -> pure Nothing
                    let verdicts = Map.insert (key, token) (isJust stepped) (searchVerdicts search)
                    case stepped of
                        Just walker' -> do
                            key' <- stateKey environment (walkerVariables start) walker'
                            forward
                                environment
                                startKey
                                leaves'
                                search{searchStack = Frame token frozen walker' key' : searchStack search, searchVerdicts = verdicts}
                                rest
                                (depth + 1)
                                start
                                size
                                program
                        Nothing -> do
                            restore environment frozen
                            pure search{searchDead = markDead dead (searchDead search), searchVerdicts = verdicts}
    headMaybe xs = case xs of
        x : _ -> Just x
        [] -> Nothing
    lastMaybe xs = headMaybe (reverse xs)
    anyM predicate = foldr (\x rest -> predicate x >>= \yes -> if yes then pure True else rest) (pure False)
    -- The verdict of 'complete' and the steps that the table killed are
    -- counted here; 'step' counts its own known verdicts.
    countKnown environment known
        | known = pure ()
        | otherwise = liftIO $ modifyIORef' (environmentCounters environment) $ \c -> c{countKnownDead = countKnownDead c + 1}
    commonPrefix (x : xs) (y : ys) | x == y = 1 + commonPrefix xs ys
    commonPrefix _ _ = 0
    readCounters environment = liftIO (readIORef (environmentCounters environment))

{- | The types of a candidate at the type heads of a query: each
higher-kinded type variable ('higherKinded') replaced by a head, when GHC
solves the class constraints on the heads under the hole's givens. So
@fmap@ gets a type at @Maybe@ when the instances give @Functor Maybe@, and
at @m@ when the signature gives @Monad m@. GHC still checks each use of the
candidate with its own type.
-}
specializations :: Environment -> [Type] -> Type -> TcM [Type]
specializations environment heads typ
    | null higher = pure []
    | otherwise = fmap catMaybes . forM (mapM (const heads) higher) $ \choice -> do
        let instantiate = substTyWith higher choice
            remaining = filter (`notElem` higher) variables
            theta' = map instantiate theta
            closed = [predicate | predicate <- theta', not (any (`elemVarSet` tyCoVarsOfType predicate) remaining)]
        solved <- entails environment closed
        pure (if solved then Just (mkSpecSigmaTy remaining theta' (instantiate rho)) else Nothing)
  where
    higher = higherKinded typ
    (variables, theta, rho) = tcSplitNestedSigmaTys typ

{- | Whether a program fits, from a walker: every step, then the end. The
walker's unification variables are as before afterwards.
-}
fitsFrom :: Environment -> Map Text Leaf -> Walker -> [Token] -> TcM Bool
fitsFrom environment leaves start tokens = do
    frozen <- freeze environment start
    result <- go start tokens
    restore environment frozen
    pure result
  where
    go walker remaining = case remaining of
        [] -> complete environment walker
        (name, children) : rest -> case Map.lookup name leaves of
            Just leaf -> step environment walker leaf children False >>= maybe (pure False) (`go` rest)
            Nothing -> pure False

-- | The program with each of its argument subterms in turn replaced by a leaf.
replacements :: Text -> Program -> [Program]
replacements leaf program = case program of
    Var _ -> []
    App function argument ->
        App function (Var leaf)
            : [App function' argument | function' <- replacements leaf function]
                <> [App function argument' | argument' <- replacements leaf argument]

-- | A leaf of a program in preorder: its name and its number of children.
type Token = (Text, Int)

-- | A program in preorder: each head leaf with its number of children.
preorder :: Program -> [Token]
preorder program = (name, length arguments) : concatMap preorder arguments
  where
    (name, arguments) = spine program
    spine (Var leaf) = (leaf, [])
    spine (App function argument) = let (leaf, rest) = spine function in (leaf, rest <> [argument])

{- | A checked step of the current program: its token, the frozen variables
before the step, and the walker after it, with the key of its state.
-}
data Frame = Frame
    { frameToken :: Token
    , frameFrozen :: Frozen
    , frameWalker :: Walker
    , frameKey :: StateKey
    }

-- | The token of the end of a program, for the verdict of 'complete'.
endToken :: Token
endToken = ("", -1)

{- | The state of a search: the frames of the current program, innermost
first, the dead prefixes, the verdicts of the steps by state and token, and
the counts.
-}
data Search = Search
    { searchStack :: [Frame]
    , searchDead :: Dead
    , searchVerdicts :: Map (StateKey, Token) Bool
    , searchReported :: Set [Token]
    -- ^ The fits so far.
    , searchPrograms :: !Int
    , searchSkipped :: !Int
    , searchFits :: !Int
    , searchSize :: !Int
    , searchLastFit :: Maybe Fit
    -- ^ The last program, when it fits.
    , searchOutOfTime :: !Bool
    , searchBuild :: !Word64
    , searchReduce :: !Word64
    , searchList :: !Word64
    , searchCheck :: !Word64
    }

-- | A search before its first program.
emptySearch :: Search
emptySearch = Search [] emptyDead Map.empty Set.empty 0 0 0 0 Nothing False 0 0 0 0

{- | Evaluate a value to weak head normal form, and give the nanoseconds that
it took; the value is 'Nothing' when the deadline comes first. Only a pure
value is stopped: a step in 'TcM' that stops part way would leave
unification variables filled.
-}
timed :: Maybe Word64 -> a -> IO (Maybe a, Word64)
timed deadline value = do
    begin <- getMonotonicTimeNSec
    result <- case deadline of
        Nothing -> Just <$> evaluate value
        Just end
            | begin >= end -> pure Nothing
            | otherwise -> timeout (fromIntegral ((end - begin) `div` 1000)) (evaluate value)
    end' <- getMonotonicTimeNSec
    pure (result, end' - begin)

-- | A trie of dead prefixes: whether the prefix so far is dead, and the longer prefixes.
data Dead = Dead !Bool !(Map Token Dead)

-- | No dead prefix.
emptyDead :: Dead
emptyDead = Dead False Map.empty

-- | Whether a prefix of the tokens is dead.
isDead :: [Token] -> Dead -> Bool
isDead tokens (Dead dead next)
    | dead = True
    | otherwise = case tokens of
        [] -> False
        token : rest -> maybe False (isDead rest) (Map.lookup token next)

-- | Mark a prefix dead.
markDead :: [Token] -> Dead -> Dead
markDead tokens (Dead dead next) = case tokens of
    [] -> Dead True Map.empty
    token : rest -> Dead dead (Map.insert token (markDead rest (Map.findWithDefault emptyDead token next)) next)
