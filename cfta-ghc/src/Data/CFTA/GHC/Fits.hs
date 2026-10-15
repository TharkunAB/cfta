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
* With 'optionCurried', the default, Hectare's types are curried
  ('Data.CFTA.Gen.Synthesis.Encoding'), and every bound type variable of
  kind @* -> *@, as the @f@ of @fmap@ and the @t@ of @length@, stays a
  variable of that kind ('eraseCurried'). It ranges over the type heads of
  kind @* -> *@ of the candidates' types and of the query at which an
  instance of each of its classes can hold ('mayHold'), so @length@ can take
  the @Maybe@ that @lookup@ gives. Then no candidate has specializations.
* With 'optionOnlyDefaulted' too, such a variable that the program does
  not determine, as the @t@ of @length (pure x)@, takes only the list type,
  when one of its classes has that default under GHC's
  @ExtendedDefaultRules@ (@Foldable@ or @Traversable@). Else Hectare drops
  the program ('Data.CFTA.Gen.Synthesis.OnlyDefault'). The check of a
  complete program has @ExtendedDefaultRules@, as GHCi does, so
  @length (pure x)@ fits.
* With 'optionTypeDomains' too, a bound type variable of kind @Type@ with
  classes that the instances decide ('decides'), as the @a@ of @maximum@,
  ranges over the types of kind @Type@ in scope at which an instance of
  each of those classes can hold: the type constructors of the candidates'
  types and of the query, the function type, and a rigid variable of the
  query that an instance matches. So @maximum@ does not have a rigid goal
  @a@ without a given @Ord a@.
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
* The mode ('optionMode') says where the programs come from: Hectare's
  programs (mode (a), the default), or the programs of states built from
  GHC's own goals, without erasure (mode (b), "Data.CFTA.GHC.States"). The
  fits of both get the check below.
* The figures of a search give the time of each part: Hectare's
  construction, reduction, and listing, and the checks in the
  typechecker.
* Each fit tells whether it ignores part of itself, by an exact check in
  GHC's terms: by parametricity, a program cannot use a subterm when it
  still fits with a value of a fresh rigid type in the place of that
  subterm. Such a fit, as @const xs n@ or @const (length xs) p@, has a
  smaller program that does the same.
* With 'optionNormalForms', each fit has a normal form
  ("Data.CFTA.GHC.NormalForm"): the bodies of the components, as @flip@,
  @fst@, and @maybe@, unfold from GHC's unfoldings. A fit with the normal form of an
  earlier fit is the same program, as @flip filter xs p@ is @filter p xs@,
  and the search skips it. A fit whose normal form drops an argument, as
  @curry snd n (f x)@, which is @f x@, does the same as a smaller program,
  and it comes last, as a fit that ignores a part does.

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
    Mode (..),
    defaultOptions,
    hectareAvoid,

    -- * Fits
    Fit (..),
    comesLast,
    Statistics (..),
    synthesizeFits,
    streamFits,

    -- * Normal forms
    normalFormsOf,
) where

import Control.Applicative ((<|>))
import Control.Exception (evaluate)
import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (atomicModifyIORef', modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (nub, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)

import Data.CFTA.GHC.Erase (
    anyResult,
    curriedClasses,
    erase,
    eraseCurried,
    eraseHead,
    higherKinded,
    typeClasses,
    typeHeads,
 )
import Data.CFTA.GHC.Internal.Check
import Data.CFTA.GHC.NormalForm (NormalForm, mentions, normalForm, termOfId)
import Data.CFTA.GHC.States (holeGoals)
import Data.CFTA.Gen.Synthesis (Defaulting (..), Encoding (..), Program (..))
import qualified Data.CFTA.Gen.Synthesis as Hectare
import Data.CFTA.Gen.Synthesis.States (Figures, searchStates)
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
import GHC.Builtin.Names (eqClassName, foldableClassName, ordClassName, showClassName, traversableClassName)
import GHC.Builtin.Types (liftedTypeKind, listTyCon)
import GHC.Builtin.Types.Prim (alphaTy, betaTy)
import GHC.Core.Class (className)
import GHC.Core.ConLike (ConLike (RealDataCon))
import GHC.Core.DataCon (dataConName, dataConNonlinearType, dataConWrapId)
import GHC.Core.InstEnv (lookupInstEnv)
import GHC.Core.Predicate (mkClassPred)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.FVs (tyCoVarsOfType, tyCoVarsOfTypesList)
import GHC.Core.TyCon (isAlgTyCon, isClassTyCon, tyConResKind, tyConTyVars)
import GHC.Core.Type (
    Type,
    expandTypeSynonyms,
    getTyVar_maybe,
    mkTyConApp,
    mkTyVarTy,
    mkTyVarTys,
    mkVisFunTyMany,
    splitAppTys,
    substTyWith,
    tyConAppTyCon_maybe,
    tyConsOfType,
 )
import GHC.Data.Bag (bagToList, emptyBag)
import GHC.Tc.Errors.Hole.FitTypes (TypedHole (..))
import GHC.Tc.Types.Constraint (Implication (..), ctEvPred)
import GHC.Tc.Types.Origin (SkolemInfoAnon (RuntimeUnkSkol))
import GHC.Tc.Utils.Env (tcGetInstEnvs, tcLookupGlobal)
import GHC.Tc.Utils.Monad (TcM, tryM)
import GHC.Tc.Utils.TcMType (newImplication, newTcEvBinds)
import GHC.Tc.Utils.TcType (TcLevel, TcTyVar, mkSpecSigmaTy, tcSplitNestedSigmaTys)
import GHC.Types.Id (Id, idType, isDataConWorkId_maybe, isDataConWrapId_maybe)
import GHC.Types.Name (Name, getName, getOccString, isExternalName, nameModule_maybe)
import GHC.Types.TyThing (TyThing (AConLike, AnId))
import GHC.Types.Unique.Set (nonDetEltsUniqSet, unionManyUniqSets)
import GHC.Types.Var (EvVar, isTyVar, tyVarKind)
import GHC.Types.Var.Set (elemVarSet)
import GHC.Unit.Module (getModule)

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
head an application, whether every fit must use it, and the name of its
identifier, if it has one. A closed type is instantiated at each use; a type
with free type variables keeps them. The name finds the identifier, whose
unfolding is the body of the candidate in the normal forms
('normalFormsOf').
-}
data Candidate = Candidate
    { candidateName :: Text
    , candidateType :: Type
    , candidateHeads :: Bool
    , candidateRequired :: Bool
    , candidateOrigin :: Maybe Name
    }

{- | An identifier as a candidate with the given text, which can head an
application and is not required. A data constructor's arrows are linear in
its identifier's type (@a %1 -> [a] %1 -> [a]@), so its candidate has the
type with unrestricted arrows, 'dataConNonlinearType', as GHC's own hole
fits use. The origin of a data constructor is the constructor's name.
-}
candidateFromId :: Text -> Id -> Candidate
candidateFromId name identifier = Candidate name typ True False (Just origin)
  where
    constructor = isDataConWrapId_maybe identifier <|> isDataConWorkId_maybe identifier
    typ = maybe (idType identifier) dataConNonlinearType constructor
    origin = maybe (getName identifier) dataConName constructor

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
    , optionMode :: Mode
    -- ^ Where the programs come from.
    , optionReport :: Maybe (Int -> Statistics -> IO ())
    -- ^ A function to call after each size.
    , optionTrace :: Maybe (Int -> Program -> IO ())
    -- ^ A function to call before each program is checked, with its size.
    , optionCurried :: Bool
    {- ^ Curried types in Hectare, with the variables of kind @* -> *@ kept,
    and no specializations. With 'False', Hectare's first-order types.
    -}
    , optionOnlyDefaulted :: Bool
    {- ^ With 'optionCurried': a variable of kind @* -> *@ that a program
    does not determine takes only its default, the list type, and the check
    has @ExtendedDefaultRules@.
    -}
    , optionTypeDomains :: Bool
    {- ^ With 'optionCurried': a variable of kind @Type@ with classes that
    the instances decide ranges over the types of the scope at which an
    instance of each of those classes can hold.
    -}
    , optionNormalForms :: Bool
    {- ^ Whether to use the normal forms of the fits: a fit with the normal
    form of an earlier fit is skipped, and a fit whose normal form drops an
    argument comes last ('fitDropsArgument').
    -}
    }

-- | A way to propose the programs of a hole.
data Mode
    = -- | Hectare's programs over the erased candidates (mode (a)).
      Hectare
    | -- | The programs of states of GHC's own goals (mode (b), "Data.CFTA.GHC.States").
      States
    deriving (Eq, Show, Read)

-- | Programs of up to five leaves, the first ten fits, mode (a), no other limit, with Hectare's curried types and normal forms.
defaultOptions :: Options
defaultOptions =
    Options
        { optionMaximumSize = 5
        , optionFits = 10
        , optionMaximumPrograms = Nothing
        , optionSeconds = Nothing
        , optionAvoid = []
        , optionMode = Hectare
        , optionReport = Nothing
        , optionTrace = Nothing
        , optionCurried = True
        , optionOnlyDefaulted = False
        , optionTypeDomains = False
        , optionNormalForms = True
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
    , fitDropsArgument :: Bool
    {- ^ With 'optionNormalForms': whether the normal form of the program
    does not use one of the required candidates (the arguments of the
    query). Then a smaller program does the same.
    -}
    }
    deriving (Eq, Show)

{- | Whether a fit comes after the others: it ignores a part
('fitIgnoresPart'), or its normal form drops an argument
('fitDropsArgument'). Either way, a smaller program does the same.
-}
comesLast :: Fit -> Bool
comesLast fit = fitIgnoresPart fit || fitDropsArgument fit

-- | The figures of a search.
data Statistics = Statistics
    { statisticsPrograms :: !Int
    -- ^ The programs that Hectare proposed.
    , statisticsRuns :: !Int
    -- ^ The typed terms that Hectare listed, of which the programs come.
    , statisticsSkipped :: !Int
    -- ^ The programs under a dead prefix, skipped without a step.
    , statisticsFits :: !Int
    -- ^ The fits that the search gave to the caller.
    , statisticsMerged :: !Int
    -- ^ The fits that the search skipped: each had the normal form of an earlier fit.
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
    , statisticsNormalNanos :: !Word64
    -- ^ The time of the normal forms of the fits.
    , statisticsCounters :: !Counters
    , statisticsStates :: Maybe Figures
    -- ^ The figures of the states of mode (b), when it ran.
    }
    deriving (Eq, Show)

{- | The first fits of a hole, as many as 'optionFits'. The search stops
after so many fits that use every part of themselves; a fit that ignores a
part or drops an argument ('comesLast') comes after them.
-}
synthesizeFits :: Options -> TypedHole -> [Candidate] -> Type -> TcM [Fit]
synthesizeFits options hole candidates goal = do
    found <- liftIO (newIORef [])
    _ <-
        streamFits options hole candidates goal $ \fit -> do
            fits <- liftIO (modifyIORef' found (fit :) >> readIORef found)
            pure (length (filter (not . comesLast) fits) < optionFits options)
    fits <- reverse <$> liftIO (readIORef found)
    pure (take (optionFits options) (filter (not . comesLast) fits <> filter comesLast fits))

{- | Check the programs of the mode ('optionMode') for a hole, in its order
(Hectare's enumeration order for mode (a)), and call the function on each
fit; stop when it returns 'False'. The result has the figures of the
search.
-}
streamFits :: Options -> TypedHole -> [Candidate] -> Type -> (Fit -> TcM Bool) -> TcM Statistics
streamFits options hole candidates goal accept = do
    environment <- (\e -> e{environmentExtendedDefaults = defaulted}) <$> newEnvironment hole
    instances <- tcGetInstEnvs
    begin <- liftIO getMonotonicTimeNSec
    let deadline = (\seconds -> begin + round (seconds * 1e9)) <$> optionSeconds options
        -- The classes that the domains of the variables of kind Type follow.
        decided cls = optionTypeDomains options && decides environment instances cls
    erased <- case optionMode options of
        Hectare -> concat <$> mapM (erasures environment decided) candidates
        States -> pure []
    let encoding
            | optionCurried options =
                Curried defaulting (domains environment instances <> typeDomains environment instances decided)
            | otherwise = FirstOrder
    -- The time of the checks of the fits' parts, which are checks too.
    ignoring <- liftIO (newIORef 0)
    -- The normal forms of the fits so far, the skipped fits, and the time of the normal forms.
    normalOf <- if optionNormalForms options then normalFormsOf candidates else pure (const Nothing)
    seen <- liftIO (newIORef Set.empty)
    merged <- liftIO (newIORef 0)
    normalizing <- liftIO (newIORef 0)
    -- The fits so far, so that a program that fits again is not a new fit.
    reported <- liftIO (newIORef Set.empty)
    figures <- liftIO (newIORef Nothing)
    let statistics progress =
            statisticsOf progress
                <$> liftIO (readIORef ignoring)
                <*> liftIO (readIORef merged)
                <*> liftIO (readIORef normalizing)
                <*> readCounters environment
                <*> liftIO (readIORef figures)
    ignoredLeaf <- rigidLeaf environment ignored
    let start = startWalker environment (map candidateType candidates) goal
        leaves' = Map.insert ignored ignoredLeaf leaves
    startKey <- stateKey environment (walkerVariables start) start
    checker <- newChecker environment leaves' start startKey
    let limits = Limits (optionMaximumSize options) (optionMaximumPrograms options) deadline
        hooks =
            Hooks
                { hookSize = \size progress -> case optionReport options of
                    Just callback -> statistics progress >>= liftIO . callback size
                    Nothing -> pure ()
                , hookProgram = \size program -> mapM_ (\trace -> liftIO (trace size program)) (optionTrace options)
                , hookNew = \tokens -> liftIO $ atomicModifyIORef' reported $ \fits ->
                    if tokens `Set.member` fits then (fits, False) else (Set.insert tokens fits, True)
                }
        -- A fit with the normal form of an earlier fit is skipped,
        -- before the checks of its parts.
        accept' fit
            | optionNormalForms options = do
                before <- liftIO getMonotonicTimeNSec
                -- A fit without a normal form (too large) is not merged.
                let normal = normalOf (Walk.fitProgram fit)
                present <- liftIO (readIORef seen)
                known <- liftIO (evaluate (maybe False (`Set.member` present) normal))
                liftIO (if known then pure () else mapM_ (modifyIORef' seen . Set.insert) normal)
                after <- liftIO getMonotonicTimeNSec
                liftIO (modifyIORef' normalizing (+ (after - before)))
                if known
                    then True <$ liftIO (modifyIORef' merged (+ 1))
                    else checkParts fit (maybe False (\form -> not (all (mentions form) required)) normal)
            | otherwise = checkParts fit False
        -- The walk gives a new fit with the hole as at the start:
        -- check the program with each argument subterm in turn of a
        -- fresh rigid type.
        checkParts fit dropsArgument = do
            before <- liftIO getMonotonicTimeNSec
            ignoresPart <- anyM (fitsFrom environment leaves' start . preorder) (replacements ignored (Walk.fitProgram fit))
            after <- liftIO getMonotonicTimeNSec
            liftIO (modifyIORef' ignoring (+ (after - before)))
            accept (Fit (Walk.fitProgram fit) (Walk.fitSize fit) ignoresPart dropsArgument)
    case optionMode options of
        -- Mode (a) needs an erased goal; mode (b) does not.
        Hectare -> case query decided erased of
            Just erasedGoal ->
                statistics
                    =<< walk
                        encoding
                        limits
                        checker
                        hooks
                        [Erased name typ (role candidate) | (candidate, name, typ) <- erased]
                        (avoid erased)
                        erasedGoal
                        accept'
            Nothing -> statistics emptyProgress
        States -> do
            goals <-
                holeGoals
                    environment
                    [(leafOf candidate, candidateRequired candidate) | candidate <- candidates]
                    (optionMaximumSize options - 1)
                    goal
            (progress, figures') <- searchStates limits checker hooks goals (optionAvoid options) accept'
            liftIO (writeIORef figures (Just figures'))
            statistics progress
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
    -- query. The k-th specialization of a candidate has the number after a
    -- space, which no Haskell name has. The curried encoding keeps the
    -- variables that the specializations replace, so there a candidate has
    -- its erased type or none.
    eraseFor decided = if optionCurried options then eraseCurried decided else erase
    erasures environment decided candidate = case eraseFor decided rigid (candidateType candidate) of
        Just typ -> pure [(candidate, candidateName candidate, typ) | keep candidate typ]
        Nothing | optionCurried options -> pure []
        Nothing -> do
            specialized <- specializations environment queryHeads (candidateType candidate)
            pure
                [ (candidate, candidateName candidate <> " " <> Text.pack (show index), typ)
                | (index, typ) <- zip [1 :: Int ..] (mapMaybe (erase rigid) specialized)
                , keep candidate typ
                ]
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
    -- The classes of each curried variable of a candidate, by their key
    -- ('curriedClasses').
    curriedKeys = Map.fromList (concatMap (curriedClasses . candidateType) candidates)
    -- The domains of the curried encoding: for each key, the type heads of
    -- kind * -> * of every candidate's type and of the query at which an
    -- instance of each of its classes can hold. A head with a bound type
    -- variable (f in the type of fmap) is not a head here.
    domains environment instances =
        let heads =
                [ head'
                | head' <- typeHeads (goal : relevant <> map (body . candidateType) candidates)
                , maybe True (isJust . rigid) (getTyVar_maybe head')
                , maybe True (isJust . rigid) (getTyVar_maybe (fst (splitAppTys head')))
                ]
            holds classes head' = all (\cls -> mayHold environment instances (mkClassPred cls [head'])) classes
         in fmap (\classes -> nub (mapMaybe (eraseHead rigid) (filter (holds classes) heads))) curriedKeys
    -- The domains of the variables of kind Type: for each key of decided
    -- classes ('typeClasses'), the types of kind Type at which an instance
    -- of each class can hold. These are the type constructors of every
    -- candidate's type and of the query, each applied to its own type
    -- variables, the function type, and the rigid variables. A rigid
    -- variable has a class only by an instance that matches it, as no given
    -- provides a decided class.
    typeDomains environment instances decided =
        let keys = Map.fromList (concatMap (typeClasses decided . candidateType) candidates)
            scope = goal : relevant <> map (body . candidateType) candidates
            constructors =
                [ mkTyConApp constructor (mkTyVarTys (tyConTyVars constructor))
                | constructor <- nonDetEltsUniqSet (unionManyUniqSets (map (tyConsOfType . expandTypeSynonyms) scope))
                , isAlgTyCon constructor
                , not (isClassTyCon constructor)
                , all ((`eqType` liftedTypeKind) . tyVarKind) (tyConTyVars constructor)
                , tyConResKind constructor `eqType` liftedTypeKind
                ]
            function = mkVisFunTyMany alphaTy betaTy
            holds classes typ = all (\cls -> mayHold environment instances (mkClassPred cls [typ])) classes
            matches classes typ = all (\cls -> let (found, _, _) = lookupInstEnv False instances cls [typ] in not (null found)) classes
            types classes =
                sort (mapMaybe (eraseHead rigid) (filter (holds classes) constructors))
                    <> [Hectare.TFun (Hectare.TVar "x0") (Hectare.TVar "x1") | holds classes function]
                    <> [ Hectare.TCons name []
                       | variable <- free
                       , tyVarKind variable `eqType` liftedTypeKind
                       , matches classes (mkTyVarTy variable)
                       , Just name <- [rigid variable]
                       ]
         in fmap types keys
    -- With optionOnlyDefaulted, the keys of the curried variables, each with
    -- whether it defaults to the list type under ExtendedDefaultRules: a
    -- key of an interactive class (of which Foldable and Traversable have
    -- kind * -> *), or the key of no class, as a variable without a
    -- constraint fits at any type head.
    defaulted = optionCurried options && optionOnlyDefaulted options
    defaulting
        | defaulted = OnlyDefault (fmap (\classes -> null classes || any interactive classes) curriedKeys)
        | otherwise = AnyHead
    interactive cls = className cls `elem` [showClassName, eqClassName, ordClassName, foldableClassName, traversableClassName]
    -- A candidate's type without its foralls and contexts, so that its heads
    -- are visible (Maybe in the type of lookup).
    body typ = let (_, _, rho) = tcSplitNestedSigmaTys typ in rho
    -- Hectare's pruning rules, with the names of every specialization.
    avoid erased =
        [ (concatMap (specializedNames erased) heads, concatMap (specializedNames erased) <$> arguments)
        | (heads, arguments) <- optionAvoid options
        ]
    specializedNames erased text = [name | (candidate, name, _) <- erased, candidateName candidate == text]
    query decided erased
        | length [() | (candidate, _, _) <- erased, candidateRequired candidate] == length (filter candidateRequired candidates) =
            eraseFor decided rigid goal
        | otherwise = Nothing
    leaves :: Map Text Leaf
    leaves = Map.fromListWith (\_ old -> old) [(candidateName c, leafOf c) | c <- candidates]
    leafOf c = Leaf (candidateName c) (candidateType c) (candidateHeads c)
    -- The name of the rigid leaf: a hole, so no candidate has it.
    ignored = "_"
    -- The names of the arguments of the query.
    required = [candidateName candidate | candidate <- candidates, candidateRequired candidate]
    statisticsOf progress ignoring skipped normalNanos counters states =
        Statistics
            (progressPrograms progress)
            (progressRuns progress)
            (progressSkipped progress)
            (progressFits progress - skipped)
            skipped
            (progressSize progress)
            (progressOutOfTime progress)
            (progressBuildNanos progress)
            (progressReduceNanos progress)
            (progressListNanos progress)
            (progressCheckNanos progress + ignoring)
            normalNanos
            counters
            states
    anyM predicate = foldr (\x rest -> predicate x >>= \yes -> if yes then pure True else rest) (pure False)
    readCounters environment = liftIO (readIORef (environmentCounters environment))

{- | The normal forms of programs over the candidates, from the unfoldings
of their identifiers ("Data.CFTA.GHC.NormalForm"). A candidate without a
name, a local variable, or a name of the current module is a leaf.
'Nothing' for a program whose normal form is too large.
-}
normalFormsOf :: [Candidate] -> TcM (Program -> Maybe NormalForm)
normalFormsOf candidates = do
    this <- getModule
    terms <- forM
        [ (candidateName candidate, name)
        | candidate <- candidates
        , Just name <- [candidateOrigin candidate]
        , isExternalName name
        , nameModule_maybe name /= Just this
        ]
        $ \(text, name) -> do
            thing <- tryM (tcLookupGlobal name)
            pure $ case thing of
                Right (AnId identifier) -> Just (text, termOfId identifier)
                Right (AConLike (RealDataCon constructor)) -> Just (text, termOfId (dataConWrapId constructor))
                _ -> Nothing
    let byName = Map.fromList (catMaybes terms)
    pure (normalForm (`Map.lookup` byName))

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
