{- | The checks of a program walk inside GHC's typechecker, on the machinery
of GHC's own hole fits ("GHC.Tc.Errors.Hole").

A walk builds a program in preorder: each step gives the leftmost open goal
a leaf (a component or a local name) with so many children. The step is a
refinement hole fit: the leaf must fit @α1 -> ... -> αk -> goal@, with a
fresh unification variable for each child, which is then the child's goal.
The check follows 'GHC.Tc.Errors.Hole.tcCheckHoleFit':

* 'tcSubTypeSigma' of the leaf's type against the refinement type, at the
  level of the hole's innermost implication, with the constraints captured.
  It instantiates the leaf's type (also the nested foralls of a class
  method) and unifies on the fly.
* The fast path: an obviously insoluble equality, as @Int ~ Bool@, kills the
  step without the solver ('checkInsoluble', copied from GHC, which does not
  export it). So does an equality of the walker that GHC's pure unifier
  ('tcUnifyTysFG') finds surely apart, with the unification variables
  bindable and the other variables rigid: GHC's unifier defers a mismatch
  to the solver (@Bool ~ t a@), and the solver call costs tens of
  microseconds.
* The solver: the wanteds of the whole program so far, cloned, and the
  hole's relevant constraints, cloned, wrapped in the hole's implications so
  that the solver has the givens, and solved with 'simplifyTopWanteds' under
  'runTcSEarlyAbort', which stops at the first insoluble constraint.

One verdict differs from 'tcCheckHoleFit', which needs every wanted solved:
a prefix keeps the wanteds of its open goals, as @Show α@ for the child of
@show@. So a prefix dies only when the solver aborts, or when an unsolved
wanted has no unification variable left; a complete program needs every
wanted solved. The solver runs on a prefix only when one of these can
happen: when the step brought an equality, or when some wanted has no
unification variable left. The solver's own unifications and defaulting are
undone after each solver call, so only the unifier's results stay.

A step writes unification variables and does not undo itself. A caller that
backtracks freezes the walker's variables before the step and restores them
after it ('freeze', 'restore'). GHC's 'GHC.Tc.Errors.Hole.withoutUnification'
makes the variables that were flexible flexible again, which is enough for
one check. It is not enough for a walk that keeps a checked prefix from one
program to the next: GHC's zonker writes the zonked type back into a filled
variable (Note [Sharing in zonking]), so a variable filled before the freeze
can come to point past a variable that the restore makes flexible again. So
a freeze here keeps the contents of every unification variable that the
walker reaches, also through filled ones, and a restore writes all of them
back.
-}
module Data.CFTA.GHC.Internal.Check (
    -- * Leaves
    Leaf (..),
    rigidLeaf,

    -- * Walks
    Environment,
    newEnvironment,
    environmentCounters,
    Walker (..),
    startWalker,
    step,
    complete,
    entails,

    -- * States
    StateKey,
    stateKey,

    -- * Freeze and restore
    Frozen,
    freeze,
    restore,

    -- * Counters
    Counters (..),
    emptyCounters,
) where

import Control.Monad (replicateM)
import Control.Monad.IO.Class (liftIO)
import Data.Bits (shiftR, (.&.), (.|.))
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as ShortByteString
import Data.Containers.ListUtils (nubOrd)
import Data.IORef (IORef, modifyIORef', newIORef, writeIORef)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)

import GHC.Builtin.Types (liftedTypeKind)
import GHC.Core.Predicate (EqRel, Pred (EqPred), classifyPredType, eqRelRole, isCallStackPredTy)
import GHC.Core.TyCo.FVs (tyCoVarsOfTypesList)
import GHC.Core.TyCo.Rep (TyLit (CharTyLit, NumTyLit, StrTyLit), Type (..), ft_af)
import GHC.Core.TyCon (TyCon, isGenerativeTyCon)
import GHC.Core.Type (PredType, anyFreeVarsOfType, coreView, mkTyVarTy, mkVisFunTysMany)
import GHC.Core.Unify (BindFlag (BindMe, DontBindMe), UnifyResultM (SurelyApart), alwaysBindFam, tcUnifyTysFG)
import GHC.Data.Bag (bagToList, listToBag, mapBag, unitBag)
import GHC.Data.FastString (unpackFS)
import GHC.Tc.Errors.Hole.FitTypes (TypedHole (..))
import GHC.Tc.Solver (simplifyTopWanteds)
import GHC.Tc.Solver.Monad (runTcSEarlyAbort)
import GHC.Tc.Types.Constraint (
    Implication (..),
    WantedConstraints (..),
    addSimples,
    andWC,
    ctEvPred,
    ctPred,
    emptyWC,
    insolubleWC,
    isSolvedWC,
    mkImplicWC,
    mkNonCanonical,
    mkSimpleWC,
 )
import GHC.Tc.Types.Origin (
    CtOrigin (ExprHoleOrigin),
    ReportRedundantConstraints (NoRRC),
    SkolemInfoAnon (RuntimeUnkSkol),
    UserTypeCtxt (ExprSigCtxt),
    mkSkolemInfo,
 )
import GHC.Tc.Utils.Monad (
    TcM,
    discardErrs,
    getTcLevel,
    liftZonkM,
    newSysName,
    setTcLevel,
    tryCaptureConstraints,
    tryTc,
 )
import GHC.Tc.Utils.TcMType (
    cloneWC,
    cloneWantedCtEv,
    newOpenFlexiTyVarTy,
    newSkolemTyVar,
    newTcEvBinds,
    newWanteds,
    readMetaTyVar,
 )
import GHC.Tc.Utils.TcType (
    MetaDetails (Flexi, Indirect),
    MetaInfo (..),
    TcLevel (..),
    TcTyVar,
    isMetaTyVar,
    metaTyVarInfo,
    metaTyVarRef,
    metaTyVarTcLevel,
 )
import GHC.Tc.Utils.Unify (tcSubTypeSigma)
import GHC.Tc.Zonk.TcType (zonkTcTypes)
import GHC.Types.Name.Occurrence (mkTyVarOcc)
import GHC.Types.Unique (Uniquable, getKey, getUnique)
import GHC.Types.Var (FunTyFlag (..), VarBndr (Bndr), isTcTyVar, tyVarKind)

{- | A leaf of a program: its name in the program, its type, and whether it
can head an application.
-}
data Leaf = Leaf
    { leafName :: Text
    , leafType :: Type
    , leafHeads :: Bool
    }

{- | A leaf of a fresh rigid type, with the given name: a new skolem of kind
@Type@ at the level of the hole. By parametricity, a program fits with this
leaf only when it does not use the leaf's value, except with 'seq'.
-}
rigidLeaf :: Environment -> Text -> TcM Leaf
rigidLeaf environment name = setTcLevel (environmentLevel environment) $ do
    information <- mkSkolemInfo RuntimeUnkSkol
    variableName <- newSysName (mkTyVarOcc "ignored")
    variable <- newSkolemTyVar information variableName liftedTypeKind
    pure (Leaf name (mkTyVarTy variable) False)

-- | The counters of a walk.
data Counters = Counters
    { countSteps :: !Int
    -- ^ The steps tried.
    , countFastRejects :: !Int
    -- ^ The steps that the fast path killed: the leaf does not fit, an obviously insoluble equality, or one surely apart.
    , countSolverSkips :: !Int
    -- ^ The checks that did not need the solver.
    , countSolverCalls :: !Int
    , countSolverPrunes :: !Int
    -- ^ The solver calls that killed a step or a program.
    , countSolverNanos :: !Word64
    , countFreezes :: !Int
    , countFreezeNanos :: !Word64
    -- ^ The time of the freezes and the restores.
    , countKnownGood :: !Int
    -- ^ The steps whose solver verdict was known from an earlier step of the same state.
    , countKnownDead :: !Int
    -- ^ The steps that failed before from the same state, skipped without a check.
    , countKeyNanos :: !Word64
    -- ^ The time of the state keys.
    }
    deriving (Eq, Show)

-- | No steps yet.
emptyCounters :: Counters
emptyCounters = Counters 0 0 0 0 0 0 0 0 0 0 0

-- | The hole of a walk, the level of its innermost implication, and the walk's counters.
data Environment = Environment
    { environmentHole :: TypedHole
    , environmentLevel :: TcLevel
    , environmentCounters :: IORef Counters
    -- ^ The counters of the walks in this environment.
    }

{- | The environment of a hole. Its level is the level of the innermost
implication, or the current level when the hole has none, as in
'GHC.Tc.Errors.Hole.tcCheckHoleFit'.
-}
newEnvironment :: TypedHole -> TcM Environment
newEnvironment hole = do
    level <- case th_implics hole of
        innermost : _ -> pure (ic_tclvl innermost)
        [] -> getTcLevel
    Environment hole level <$> liftIO (newIORef emptyCounters)

{- | The state of a walk: the unification variables that a later step can
write, the wanteds of the program so far, and the goals still open, leftmost
first.
-}
data Walker = Walker
    { walkerVariables :: [TcTyVar]
    , walkerWanteds :: WantedConstraints
    , walkerGoals :: [Type]
    }

{- | A walker with one goal. Its variables are the unification variables of
the goal, of the hole's relevant constraints, and of the given types, so
that a freeze also covers the variables of the context that a step can
write.
-}
startWalker :: Environment -> [Type] -> Type -> Walker
startWalker environment types goal =
    Walker
        { walkerVariables = metasOf (goal : map ctEvPred (bagToList (th_relevant_cts (environmentHole environment))) <> types)
        , walkerWanteds = emptyWC
        , walkerGoals = [goal]
        }

{- | The state of a walker up to the names of its unification variables:
its goals, its wanteds, the hole's relevant constraints, and the given
unification variables (of the goal and of the candidates' types, which a
step can fill without a trace in the goals), all zonked. Each unification
variable becomes a number in the order of its first occurrence, with its
level, its kind of variable, and its kind. A step of two walkers with the
same key and the same leaf gives the same verdict.
-}
newtype StateKey = StateKey ShortByteString
    deriving (Eq, Ord)

-- | The key of a walker's state, with the given unification variables.
stateKey :: Environment -> [TcTyVar] -> Walker -> TcM StateKey
stateKey environment given walker = do
    start <- liftIO getMonotonicTimeNSec
    types <-
        liftZonkM . zonkTcTypes $
            walkerGoals walker
                <> wantedPredicates (walkerWanteds walker)
                <> map ctEvPred (bagToList (th_relevant_cts (environmentHole environment)))
                <> map mkTyVarTy given
    let key = StateKey (encode (typesKey types))
    end <- key `seq` liftIO getMonotonicTimeNSec
    liftIO $ modifyIORef' (environmentCounters environment) $ \c -> c{countKeyNanos = countKeyNanos c + (end - start)}
    pure key
  where
    -- Seven bits to a byte; the last byte of a number is under 128.
    encode = ShortByteString.pack . concatMap bytes
    bytes number
        | number < 128 = [fromIntegral number]
        | otherwise = fromIntegral (number .&. 127 .|. 128) : bytes (number `shiftR` 7)

{- | Types as numbers: a tag for each form of type, then its parts. A
unification variable is its number in the order of first occurrence; the
first occurrence also gives its level, its kind of variable, and its kind.
Another variable, a type constructor, or a binder is its unique.
-}
typesKey :: [Type] -> [Word64]
typesKey = reverse . snd . foldl' typeKey (Map.empty, [])
  where
    typeKey (seen, out) typ = case typ of
        TyVarTy variable
            | isTcTyVar variable && isMetaTyVar variable -> case Map.lookup (unique variable) seen of
                Just index -> (seen, index : 1 : out)
                Nothing ->
                    let index = fromIntegral (Map.size seen)
                     in typeKey
                            (Map.insert (unique variable) index seen, info variable : level variable : index : 1 : out)
                            (tyVarKind variable)
            | otherwise -> (seen, unique variable : 2 : out)
        TyConApp constructor arguments ->
            foldl' typeKey (seen, fromIntegral (length arguments) : unique constructor : 3 : out) arguments
        FunTy flag multiplicity argument result -> foldl' typeKey (seen, flagKey flag : 4 : out) [multiplicity, argument, result]
        AppTy function argument -> foldl' typeKey (seen, 5 : out) [function, argument]
        ForAllTy (Bndr variable _) body -> foldl' typeKey (seen, unique variable : 6 : out) [tyVarKind variable, body]
        LitTy literal ->
            let text = case literal of
                    NumTyLit number -> 'n' : show number
                    StrTyLit string -> 's' : unpackFS string
                    CharTyLit character -> ['c', character]
             in (seen, reverse (map (fromIntegral . fromEnum) text) <> (fromIntegral (length text) : 7 : out))
        CastTy inner _ -> typeKey (seen, 8 : out) inner
        CoercionTy _ -> (seen, 9 : out)
    unique :: (Uniquable a) => a -> Word64
    unique = getKey . getUnique
    level variable = case metaTyVarTcLevel variable of
        TcLevel depth -> fromIntegral depth + 1
        QLInstVar -> 0
    info variable = case metaTyVarInfo variable of
        TauTv -> 0
        TyVarTv -> 1
        RuntimeUnkTv -> 2
        CycleBreakerTv -> 3
        ConcreteTv _ -> 4
    flagKey flag = case flag of
        FTF_T_T -> 0
        FTF_T_C -> 1
        FTF_C_T -> 2
        FTF_C_C -> 3

-- | The unification variables of types.
metasOf :: [Type] -> [TcTyVar]
metasOf = filter (\variable -> isTcTyVar variable && isMetaTyVar variable) . tyCoVarsOfTypesList

{- | Give the leftmost open goal a leaf with so many children. 'Nothing' when
the leaf does not fit, or when a wanted cannot be solved any more. With
'True' for the last argument, the wanteds are known to be good (an earlier
step of a walker with the same 'StateKey' and the same leaf passed), so the
solver does not run. The step writes unification variables; freeze before
it to undo it.
-}
step :: Environment -> Walker -> Leaf -> Int -> Bool -> TcM (Maybe Walker)
step environment walker leaf children known = case walkerGoals walker of
    [] -> pure Nothing
    goal : rest
        | children > 0 && not (leafHeads leaf) -> pure Nothing
        | otherwise -> setTcLevel (environmentLevel environment) . discardErrs $ do
            count (\c -> c{countSteps = countSteps c + 1})
            arguments <- replicateM children newOpenFlexiTyVarTy
            (fitted, wanted) <-
                tryCaptureConstraints $
                    tcSubTypeSigma (ExprHoleOrigin Nothing) (ExprSigCtxt NoRRC) (leafType leaf) (mkVisFunTysMany arguments goal)
            if isNothing fitted || checkInsoluble wanted
                then Nothing <$ count (\c -> c{countFastRejects = countFastRejects c + 1})
                else do
                    -- The new variables are the children's goals and the ones
                    -- of the new wanteds; a freeze reaches the leaf's
                    -- instance through the filled goal.
                    let walker' =
                            Walker
                                { walkerVariables =
                                    nubOrd (metasOf (arguments <> map ctPred (bagToList (wc_simple wanted))) <> walkerVariables walker)
                                , walkerWanteds = wanted `andWC` walkerWanteds walker
                                , walkerGoals = arguments <> rest
                                }
                    ok <-
                        if known
                            then True <$ count (\c -> c{countKnownGood = countKnownGood c + 1})
                            else satisfiable environment walker' (hasEquality wanted) False
                    pure (if ok then Just walker' else Nothing)
  where
    count = liftIO . modifyIORef' (environmentCounters environment)
    hasEquality wanted = any (isEquality . classifyPredType . ctPred) (bagToList (wc_simple wanted))
    isEquality predicate = case predicate of
        EqPred{} -> True
        _ -> False

-- | Whether a walker has no open goal and every wanted is solved under the givens.
complete :: Environment -> Walker -> TcM Bool
complete environment walker
    | null (walkerGoals walker) =
        setTcLevel (environmentLevel environment) (discardErrs (satisfiable environment walker False True))
    | otherwise = pure False

{- | Whether GHC solves the predicates under the hole's givens, with the
instances in scope, as for a complete program. The solver's unifications
do not stay.
-}
entails :: Environment -> [PredType] -> TcM Bool
entails environment predicates = setTcLevel (environmentLevel environment) . discardErrs $ do
    evidence <- newWanteds (ExprHoleOrigin Nothing) predicates
    satisfiable environment (Walker (metasOf predicates) (mkSimpleWC evidence) []) False True

{- | Whether the wanteds of a walker can still be solved. With the last
'True', every wanted must be solved, as for a complete program. Otherwise
the solver runs only when the step brought an equality (the third
argument), or when some wanted has no unification variable left; only those
can make a prefix fail. An equality that is surely apart fails without the
solver.
-}
satisfiable :: Environment -> Walker -> Bool -> Bool -> TcM Bool
satisfiable environment walker equality finished = do
    current <- liftZonkM (zonkTcTypes (filter (not . isCallStackPredTy) (wantedPredicates (walkerWanteds walker))))
    if any apart current
        then False <$ count (\c -> c{countFastRejects = countFastRejects c + 1})
        else
            if not finished && not equality && all open current
                then True <$ count (\c -> c{countSolverSkips = countSolverSkips c + 1})
                else do
                    start <- liftIO getMonotonicTimeNSec
                    -- The solver's own unifications and defaulting do not stay.
                    frozen <- freeze environment walker
                    residual <- solve
                    unsolved <- liftZonkM (zonkTcTypes (maybe [] (filter (not . isCallStackPredTy) . wantedPredicates) residual))
                    restore environment frozen
                    end <- liftIO getMonotonicTimeNSec
                    let answer = case residual of
                            Nothing -> False
                            Just remaining
                                | insolubleWC remaining -> False
                                | finished -> isSolvedWC remaining
                                | otherwise -> all open unsolved
                    count $ \c ->
                        c
                            { countSolverCalls = countSolverCalls c + 1
                            , countSolverPrunes = countSolverPrunes c + (if answer then 0 else 1)
                            , countSolverNanos = countSolverNanos c + (end - start)
                            }
                    pure answer
  where
    apart predicate = case classifyPredType predicate of
        EqPred _ left right -> case tcUnifyTysFG alwaysBindFam bindable [left] [right] of
            SurelyApart -> True
            _ -> False
        _ -> False
    bindable variable _ = if isTcTyVar variable && isMetaTyVar variable then BindMe else DontBindMe
    open = anyFreeVarsOfType (\variable -> isTcTyVar variable && isMetaTyVar variable)
    count = liftIO . modifyIORef' (environmentCounters environment)
    hole = environmentHole environment
    -- As in tcCheckHoleFit: clone the wanteds and the relevant constraints
    -- (they may hold evidence holes, #15370), wrap them in the hole's
    -- implications for the givens, and abort at the first insoluble one.
    solve = do
        wanteds <- cloneWC (walkerWanteds walker)
        relevants <- traverse cloneWantedCtEv (bagToList (th_relevant_cts hole))
        binds <- newTcEvBinds
        let wrap constraints implication = mkImplicWC (unitBag implication{ic_wanted = constraints, ic_binds = binds})
            wrapped = foldl wrap (addSimples wanteds (mapBag mkNonCanonical (listToBag relevants))) (th_implics hole)
        (remaining, _) <- tryTc (runTcSEarlyAbort (simplifyTopWanteds wrapped))
        pure remaining

-- | The predicates of wanted constraints, also the ones inside implications.
wantedPredicates :: WantedConstraints -> [PredType]
wantedPredicates wanted =
    map ctPred (bagToList (wc_simple wanted)) <> concatMap (wantedPredicates . ic_wanted) (bagToList (wc_impl wanted))

{- | Whether the constraints have an obviously insoluble equality, as
@Int ~ Bool@. This is the fast path of 'GHC.Tc.Errors.Hole.tcCheckHoleFit',
copied because GHC does not export it: the on-the-fly unifier has already
decomposed the equalities, so a mismatch of generative type constructors at
the top is enough.
-}
checkInsoluble :: WantedConstraints -> Bool
checkInsoluble wanted = any (insoluble . classifyPredType . ctPred) (bagToList (wc_simple wanted))
  where
    insoluble predicate = case predicate of
        EqPred relation left right -> definitelyNotEqual relation left right
        _ -> False

-- | Whether two types can never be equal: generative type constructors that differ at the top.
definitelyNotEqual :: EqRel -> Type -> Type -> Bool
definitelyNotEqual relation = go
  where
    role = eqRelRole relation
    go left right
        | Just left' <- coreView left = go left' right
        | Just right' <- coreView right = go left right'
    go (TyConApp constructor _) right | isGenerativeTyCon constructor role = differs constructor right
    go left (TyConApp constructor _) | isGenerativeTyCon constructor role = differs constructor left
    go left@FunTy{} right@FunTy{} = ft_af left /= ft_af right
    go _ _ = False
    differs :: TyCon -> Type -> Bool
    differs constructor other = case other of
        TyConApp constructor' _ | isGenerativeTyCon constructor' role -> constructor /= constructor'
        FunTy{} -> True
        ForAllTy{} -> True
        _ -> False

-- | The contents of unification variables at a freeze.
newtype Frozen = Frozen [(TcTyVar, MetaDetails)]

{- | Keep the contents of every unification variable that the walker reaches,
also through filled variables.
-}
freeze :: Environment -> Walker -> TcM Frozen
freeze environment walker = do
    start <- liftIO getMonotonicTimeNSec
    frozen <- reach Set.empty [] (walkerVariables walker)
    end <- liftIO getMonotonicTimeNSec
    liftIO $ modifyIORef' (environmentCounters environment) $ \c ->
        c{countFreezes = countFreezes c + 1, countFreezeNanos = countFreezeNanos c + (end - start)}
    pure (Frozen frozen)
  where
    reach _ found [] = pure found
    reach seen found (variable : rest)
        | variable `Set.member` seen = reach seen found rest
        | otherwise = do
            details <- readMetaTyVar variable
            let more = case details of
                    Indirect filled -> metasOf [filled]
                    Flexi -> []
            reach (Set.insert variable seen) ((variable, details) : found) (more <> rest)

{- | Write the frozen contents back to the variables' references. This undoes
the unifier, the solver, and the zonker's write-backs, so it restores the
zonked types exactly.
-}
restore :: Environment -> Frozen -> TcM ()
restore environment (Frozen frozen) = do
    start <- liftIO getMonotonicTimeNSec
    mapM_ (\(variable, details) -> liftIO (writeIORef (metaTyVarRef variable) details)) frozen
    end <- liftIO getMonotonicTimeNSec
    liftIO $ modifyIORef' (environmentCounters environment) $ \c ->
        c{countFreezeNanos = countFreezeNanos c + (end - start)}
