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
* The search has two stages. When the first stage ends, or uses half of the
  time, with too few fits, the second stage runs for the rest of the time.
  It also proposes a candidate with a @Foldable@ or @Traversable@ type
  variable, which the erasure makes a list, at the other type heads of the
  query and at the closed heads of the components' results: so @sum@ at
  @Maybe@ for @Maybe Int -> Int@, and @length@ at the @Maybe@ of @lookup@ in
  @length (lookup k xs)@. The first stage stays as fast as before where the
  erasure keeps what the query needs.
* Each program is checked in preorder, one leaf at a time
  ("Data.CFTA.GHC.Internal.Check"), as a refinement hole fit, with the
  parts of 'GHC.Tc.Errors.Hole.tcCheckHoleFit': 'tcSubTypeSigma' at the
  level of the innermost implication, the fast path for obviously insoluble
  equalities, and the solver with early abort inside the hole's
  implications.
* The walk ("Data.CFTA.Gen.Synthesis.Walk", which does not depend on GHC)
  keeps the checked prefix of the last program. The next program
  backtracks to the longest prefix that it shares with the last one, by a
  restore of the frozen unification variables, and checks only the rest. A
  prefix that fails goes into a trie of dead prefixes, so every later
  program under it is skipped without a step. Here the walk's checker is
  GHC's: a stack of frames, each with the frozen variables before its step.
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
import Control.Monad (forM, unless)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (nub, nubBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)

import Data.CFTA.GHC.Erase (anyResult, erase, higherKinded, listKinded, typeHeads)
import Data.CFTA.GHC.Internal.Check
import Data.CFTA.Gen.Synthesis (Program (..))
import Data.CFTA.Gen.Synthesis.Walk (
    Checker (..),
    Erased (..),
    Extension (..),
    Hooks (..),
    Limits (..),
    Progress (..),
    Role (..),
    Token,
    emptyProgress,
    preorder,
    walk,
 )
import qualified Data.CFTA.Gen.Synthesis.Walk as Walk
import GHC.Builtin.Types (listTyCon)
import GHC.Core.DataCon (dataConNonlinearType)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.FVs (tyCoVarsOfType, tyCoVarsOfTypesList)
import GHC.Core.Type (Type, substTyWith, tyConAppTyCon_maybe)
import GHC.Data.Bag (bagToList, emptyBag)
import GHC.Tc.Errors.Hole.FitTypes (TypedHole (..))
import GHC.Tc.Types.Constraint (Implication (..), ctEvPred)
import GHC.Tc.Types.Origin (SkolemInfoAnon (RuntimeUnkSkol))
import GHC.Tc.Utils.Monad (TcM)
import GHC.Tc.Utils.TcMType (newImplication, newTcEvBinds)
import GHC.Tc.Utils.TcType (TcLevel, TcTyVar, mkSpecSigmaTy, tcSplitFunTys, tcSplitNestedSigmaTys)
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
    , statisticsSecondStage :: !Bool
    -- ^ Whether the second stage ran.
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

The search has two stages, with one checker and one table of verdicts. The
first stage proposes each candidate at its erased type, or else at its
'specializations' at the type heads of the query. The second stage runs when
the first one ends, or reaches half of 'optionSeconds', with fewer fits that
use every part than 'optionFits', and the function did not stop it. It has
the rest of the time and of the programs, and also specializes the variables
that the erasure makes lists ('listKinded'). It gives only the fits that the
first stage did not give.
-}
streamFits :: Options -> TypedHole -> [Candidate] -> Type -> (Fit -> TcM Bool) -> TcM Statistics
streamFits options hole candidates goal accept = do
    environment <- newEnvironment hole
    begin <- liftIO getMonotonicTimeNSec
    let deadline fraction = (\seconds -> begin + round (seconds * fraction * 1e9)) <$> optionSeconds options
    -- The time of the checks of the fits' parts, which are checks too.
    ignoring <- liftIO (newIORef 0)
    -- The fits so far, by their tokens; the number of them that use every
    -- part; and whether the function stopped the search.
    delivered <- liftIO (newIORef Set.empty)
    using <- liftIO (newIORef (0 :: Int))
    stopped <- liftIO (newIORef False)
    ignoredLeaf <- rigidLeaf environment ignored
    let start = startWalker environment (map candidateType candidates) goal
        leaves' = Map.insert ignored ignoredLeaf leaves
    startKey <- stateKey environment (walkerVariables start) start
    checker <- newChecker environment leaves' start startKey
    let statistics second earlier progress = do
            ignoringNanos <- liftIO (readIORef ignoring)
            fits <- Set.size <$> liftIO (readIORef delivered)
            counters <- liftIO (readIORef (environmentCounters environment))
            let total part = sum (map part (progress : earlier))
            pure
                Statistics
                    { statisticsPrograms = total progressPrograms
                    , statisticsSkipped = total progressSkipped
                    , statisticsFits = fits
                    , statisticsSize = progressSize progress
                    , statisticsOutOfTime = progressOutOfTime progress
                    , statisticsSecondStage = second
                    , statisticsBuildNanos = total progressBuildNanos
                    , statisticsReduceNanos = total progressReduceNanos
                    , statisticsListNanos = total progressListNanos
                    , statisticsCheckNanos = total progressCheckNanos + ignoringNanos
                    , statisticsCounters = counters
                    }
        -- The walk gives a new fit with the hole as at the start: check the
        -- program with each argument subterm in turn of a fresh rigid type.
        deliver fit = do
            let tokens = preorder (Walk.fitProgram fit)
            known <- Set.member tokens <$> liftIO (readIORef delivered)
            if known
                then pure True
                else do
                    before <- liftIO getMonotonicTimeNSec
                    ignoresPart <- anyM (fitsFrom environment leaves' start . preorder) (replacements ignored (Walk.fitProgram fit))
                    after <- liftIO getMonotonicTimeNSec
                    liftIO $ do
                        modifyIORef' ignoring (+ (after - before))
                        modifyIORef' delivered (Set.insert tokens)
                        unless ignoresPart (modifyIORef' using (+ 1))
                    more <- accept (Fit (Walk.fitProgram fit) (Walk.fitSize fit) ignoresPart)
                    unless more (liftIO (writeIORef stopped True))
                    pure more
        -- One stage, after the stages before it.
        stage second deadline' programs earlier = do
            erased <- concat <$> mapM (erasures environment second) candidates
            let hooks =
                    Hooks
                        { hookSize = \size progress -> case optionReport options of
                            Just callback -> statistics second earlier progress >>= liftIO . callback size
                            Nothing -> pure ()
                        , hookProgram = \size program -> mapM_ (\trace -> liftIO (trace size program)) (optionTrace options)
                        }
            case query erased of
                Just erasedGoal ->
                    walk
                        (Limits (optionMaximumSize options) programs deadline')
                        checker
                        hooks
                        [Erased name typ (role candidate) | (candidate, name, typ) <- erased]
                        (avoid erased)
                        erasedGoal
                        deliver
                Nothing -> pure emptyProgress
    first <- stage False (deadline 0.5) (optionMaximumPrograms options) []
    done <- liftIO (readIORef stopped)
    enough <- (>= optionFits options) <$> liftIO (readIORef using)
    let programs = subtract (progressPrograms first) <$> optionMaximumPrograms options
    if done || enough || maybe False (<= 0) programs
        then statistics False [] first
        else stage True (deadline 1) programs [first] >>= statistics True [first]
  where
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
    -- query. In the second stage, a candidate with a variable that the
    -- erasure makes a list has its specializations too. The k-th
    -- specialization of a candidate has the number after a space, which no
    -- Haskell name has.
    erasures environment second candidate = case erase rigid typ of
        Just erased | null heads || null (listKinded typ) -> pure [(candidate, candidateName candidate, erased) | keep candidate erased]
        _ -> do
            specialized <- specializations environment queryHeads heads typ
            pure
                [ (candidate, candidateName candidate <> " " <> Text.pack (show index), erased)
                | (index, erased) <- zip [1 :: Int ..] (mapMaybe (erase rigid) specialized)
                , keep candidate erased
                ]
      where
        typ = candidateType candidate
        heads = if second then listHeads else []
    keep candidate typ = candidateRequired candidate || not (anyResult typ)
    role candidate
        | candidateRequired candidate = Required
        | candidateHeads candidate = Component
        | otherwise = ArgumentOnly
    -- The list head is left out: the list functions already cover it (map
    -- for fmap, concatMap for (>>=)), and its specializations would repeat
    -- their fits.
    queryHeads =
        filter
            ((/= Just listTyCon) . tyConAppTyCon_maybe)
            (typeHeads (goal : [candidateType candidate | candidate <- candidates, candidateRequired candidate]))
    -- The heads of the second stage for a variable that the erasure makes a
    -- list: the query's, and the closed heads of the components' results,
    -- as the Maybe of lookup, which a program can pass on to sum.
    listHeads =
        nubBy eqType $
            queryHeads
                <> filter
                    (\head' -> null (tyCoVarsOfTypesList [head']) && tyConAppTyCon_maybe head' /= Just listTyCon)
                    ( typeHeads
                        [snd (tcSplitFunTys rho) | candidate <- candidates, let (_, _, rho) = tcSplitNestedSigmaTys (candidateType candidate)]
                    )
    -- Hectare's pruning rules, with the names of every specialization.
    avoid erased =
        [ (concatMap (specializedNames erased) heads, concatMap (specializedNames erased) <$> arguments)
        | (heads, arguments) <- optionAvoid options
        ]
    specializedNames erased text = [name | (candidate, name, _) <- erased, candidateName candidate == text]
    query erased
        | length [() | (candidate, _, _) <- erased, candidateRequired candidate] == length (filter candidateRequired candidates) =
            erase rigid goal
        | otherwise = Nothing
    leaves :: Map Text Leaf
    leaves =
        Map.fromListWith
            (\_ old -> old)
            [(candidateName c, Leaf (candidateName c) (candidateType c) (candidateHeads c)) | c <- candidates]
    -- The name of the rigid leaf: a hole, so no candidate has it.
    ignored = "_"
    anyM predicate = foldr (\x rest -> predicate x >>= \yes -> if yes then pure True else rest) (pure False)

{- | A checked step of the current program: the frozen variables before the
step, and the walker after it, with the key of its state.
-}
data Frame = Frame
    { frameFrozen :: Frozen
    , frameWalker :: Walker
    , frameKey :: StateKey
    }

-- | The token of the end of a program, for the verdict of 'complete'.
endToken :: Token
endToken = ("", -1)

{- | The checker of a walk in GHC's typechecker, from a start walker and the
key of its state. Its frames, innermost first, and the verdicts of the steps
are in references. The verdict of a step depends only on the walker's state,
up to the names of its unification variables, and on the token
('StateKey'): a step that failed before from the same state fails without a
check, and a step that passed before does not call the solver. The table
lives here, in the host, because each step's key is the host's, and a step
that is known to pass still runs in the host to fill its variables.
-}
newChecker :: Environment -> Map Text Leaf -> Walker -> StateKey -> TcM (Checker TcM)
newChecker environment leaves start startKey = do
    stack <- liftIO (newIORef [])
    verdicts <- liftIO (newIORef Map.empty)
    let
        -- One restore suffices: the first frame that goes was frozen before
        -- its step, with every variable that existed then.
        truncateTo kept = do
            frames <- liftIO (readIORef stack)
            case drop kept (reverse frames) of
                frame : _ -> restore environment (frameFrozen frame)
                [] -> pure ()
            liftIO (writeIORef stack (drop (length frames - kept) frames))
        remember key token verdict = liftIO (modifyIORef' verdicts (Map.insert (key, token) verdict))
        extend tokens = do
            frames <- liftIO (readIORef stack)
            table <- liftIO (readIORef verdicts)
            let (walker, key) = case frames of
                    frame : _ -> (frameWalker frame, frameKey frame)
                    [] -> (start, startKey)
            case tokens of
                [] -> do
                    fits <- case Map.lookup (key, endToken) table of
                        Just known -> known <$ countKnown known
                        Nothing -> complete environment walker
                    remember key endToken fits
                    pure (Done fits)
                token@(name, children) : rest -> case Map.lookup (key, token) table of
                    Just False -> Died (length frames) <$ countKnown False
                    known -> do
                        frozen <- freeze environment walker
                        stepped <- case Map.lookup name leaves of
                            Just leaf -> step environment walker leaf children (known == Just True)
                            Nothing -> pure Nothing
                        remember key token (isJust stepped)
                        case stepped of
                            Just walker' -> do
                                key' <- stateKey environment (walkerVariables start) walker'
                                liftIO (modifyIORef' stack (Frame frozen walker' key' :))
                                extend rest
                            Nothing -> Died (length frames) <$ restore environment frozen
    pure (Checker truncateTo extend)
  where
    -- The verdict of 'complete' and the steps that the table killed are
    -- counted here; 'step' counts its own known verdicts.
    countKnown known
        | known = pure ()
        | otherwise = liftIO $ modifyIORef' (environmentCounters environment) $ \c -> c{countKnownDead = countKnownDead c + 1}

{- | The types of a candidate at the type heads of a query: each
higher-kinded type variable ('higherKinded') replaced by a head, when GHC
solves the class constraints on the heads under the hole's givens. So
@fmap@ gets a type at @Maybe@ when the instances give @Functor Maybe@, and
at @m@ when the signature gives @Monad m@. With heads in the second list,
each variable that the erasure makes a list ('listKinded', as @t@ in
@length@) is also kept or replaced by one of them, so @sum@ gets a type at
@Maybe@ as well as at lists; the first type keeps every list variable, as
the erasure does. GHC still checks each use of the candidate with its own
type.
-}
specializations :: Environment -> [Type] -> [Type] -> Type -> TcM [Type]
specializations environment heads listHeads typ
    | null (higher <> lists) = pure []
    | otherwise = fmap catMaybes . forM (mapM choices (higher <> lists)) $ \choice -> do
        let replaced = [(variable, head') | (variable, Just head') <- zip (higher <> lists) choice]
            instantiate = substTyWith (map fst replaced) (map snd replaced)
            remaining = filter (`notElem` map fst replaced) variables
            theta' = map instantiate theta
            closed = [predicate | predicate <- theta', not (any (`elemVarSet` tyCoVarsOfType predicate) remaining)]
        solved <- entails environment closed
        pure (if solved then Just (mkSpecSigmaTy remaining theta' (instantiate rho)) else Nothing)
  where
    higher = higherKinded typ
    lists = if null listHeads then [] else listKinded typ
    choices variable
        | variable `elem` higher = map Just heads
        | otherwise = Nothing : map Just listHeads
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
