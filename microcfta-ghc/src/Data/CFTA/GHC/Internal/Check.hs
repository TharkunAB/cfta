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
  export it).
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

    -- * Walks
    Environment,
    newEnvironment,
    environmentCounters,
    Walker (..),
    startWalker,
    step,
    complete,

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
import Data.Containers.ListUtils (nubOrd)
import Data.IORef (IORef, modifyIORef', newIORef, writeIORef)
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)

import GHC.Core.Predicate (EqRel, Pred (EqPred), classifyPredType, eqRelRole, isCallStackPredTy)
import GHC.Core.TyCo.FVs (tyCoVarsOfTypesList)
import GHC.Core.TyCo.Rep (Type (ForAllTy, FunTy, TyConApp), ft_af)
import GHC.Core.TyCon (TyCon, isGenerativeTyCon)
import GHC.Core.Type (PredType, anyFreeVarsOfType, coreView, mkVisFunTysMany)
import GHC.Data.Bag (bagToList, listToBag, mapBag, unitBag)
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
 )
import GHC.Tc.Types.Origin (CtOrigin (ExprHoleOrigin), ReportRedundantConstraints (NoRRC), UserTypeCtxt (ExprSigCtxt))
import GHC.Tc.Utils.Monad (TcM, discardErrs, getTcLevel, liftZonkM, setTcLevel, tryCaptureConstraints, tryTc)
import GHC.Tc.Utils.TcMType (cloneWC, cloneWantedCtEv, newOpenFlexiTyVarTy, newTcEvBinds, readMetaTyVar)
import GHC.Tc.Utils.TcType (MetaDetails (Flexi, Indirect), TcLevel, TcTyVar, isMetaTyVar, metaTyVarRef)
import GHC.Tc.Utils.Unify (tcSubTypeSigma)
import GHC.Tc.Zonk.TcType (zonkTcTypes)
import GHC.Types.Var (isTcTyVar)

{- | A leaf of a program: its name in the program, its type, and whether it
can head an application.
-}
data Leaf = Leaf
    { leafName :: Text
    , leafType :: Type
    , leafHeads :: Bool
    }

-- | The counters of a walk.
data Counters = Counters
    { countSteps :: !Int
    -- ^ The steps tried.
    , countFastRejects :: !Int
    -- ^ The steps that the fast path killed: the leaf does not fit, or an obviously insoluble equality.
    , countSolverSkips :: !Int
    -- ^ The checks that did not need the solver.
    , countSolverCalls :: !Int
    , countSolverPrunes :: !Int
    -- ^ The solver calls that killed a step or a program.
    , countSolverNanos :: !Word64
    , countFreezes :: !Int
    , countFreezeNanos :: !Word64
    -- ^ The time of the freezes and the restores.
    }
    deriving (Eq, Show)

-- | No steps yet.
emptyCounters :: Counters
emptyCounters = Counters 0 0 0 0 0 0 0 0

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

-- | The unification variables of types.
metasOf :: [Type] -> [TcTyVar]
metasOf = filter (\variable -> isTcTyVar variable && isMetaTyVar variable) . tyCoVarsOfTypesList

{- | Give the leftmost open goal a leaf with so many children. 'Nothing' when
the leaf does not fit, or when a wanted cannot be solved any more. The step
writes unification variables; freeze before it to undo it.
-}
step :: Environment -> Walker -> Leaf -> Int -> TcM (Maybe Walker)
step environment walker leaf children = case walkerGoals walker of
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
                    ok <- satisfiable environment walker' (hasEquality wanted) False
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

{- | Whether the wanteds of a walker can still be solved. With the last
'True', every wanted must be solved, as for a complete program. Otherwise
the solver runs only when the step brought an equality (the third
argument), or when some wanted has no unification variable left; only those
can make a prefix fail.
-}
satisfiable :: Environment -> Walker -> Bool -> Bool -> TcM Bool
satisfiable environment walker equality finished = do
    current <- liftZonkM (zonkTcTypes (filter (not . isCallStackPredTy) (wantedPredicates (walkerWanteds walker))))
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
