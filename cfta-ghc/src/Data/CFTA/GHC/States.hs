{- | Mode (b) in GHC's typechecker: the goals of a hole for the search over
states of "Data.CFTA.Gen.Synthesis.States", without Hectare and without
erasure.

The key of a goal is its zonked type up to the names of its unification
variables ('StateKey'). A refinement of a goal is the step of the walk
("Data.CFTA.GHC.Internal.Check": 'tcSubTypeSigma' against
@α1 -> ... -> αk -> goal@, the fast checks, and the solver under the
hole's givens) of a leaf with @k@ children on a walker with only that goal,
between a freeze and a restore of its unification variables. The child
goals are the zonked goals after the step, and the first goal of a key is
the one that the later refinements of the key step on. A child goal has the
instantiation of its parent, but not the wanteds of the parent's step or of
its siblings: the walk's checker ("Data.CFTA.GHC.Fits") checks them in the
whole program.

* An index of the leaves by the head of their result type after @k@
  arguments (a type constructor, the arrow, or a rigid variable; a bound
  variable matches every head) keeps the leaves that cannot fit the head of
  a goal out of its refinement, and gives no more children to a leaf whose
  result is a concrete type that is not a function.
* The one rule of the erasure that stays: a leaf whose result is a type
  variable that no parameter has (@undefined@, @mempty@, @fromIntegral@)
  fits every goal and floods the states, so it is left out, unless each
  program must use it. Higher-kinded leaves (@fmap@, @pure@, @(>>=)@) need
  nothing more: GHC instantiates them.
-}
module Data.CFTA.GHC.States (
    holeGoals,
) where

import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)

import Data.CFTA.GHC.Internal.Check
import Data.CFTA.Gen.Synthesis.States (Goals (..), Refinement (..))
import GHC.Core.Multiplicity (scaledThing)
import GHC.Core.TyCo.FVs (tyCoVarsOfTypes)
import GHC.Core.TyCo.Rep (Type (..))
import GHC.Core.Type (expandTypeSynonyms, splitVisibleFunTy_maybe, tcSplitTyConApp_maybe)
import GHC.Tc.Types.Constraint (emptyWC)
import GHC.Tc.Utils.Monad (TcM, liftZonkM)
import GHC.Tc.Utils.TcType (isMetaTyVar, tcSplitFunTys, tcSplitNestedSigmaTys)
import GHC.Tc.Zonk.TcType (zonkTcType)
import GHC.Types.Unique (getKey, getUnique)
import GHC.Types.Var (TyVar, isTcTyVar)
import GHC.Types.Var.Set (elemVarSet)

-- | The head of a type, for the index: an exact one, or one that matches every head.
data Head = Exact !Word64 | Any
    deriving (Eq, Ord, Show)

{- | The goals of a hole for the search over states: from the environment of
the hole, the leaves (each with whether each program must use it), the
largest number of children of a leaf, and the goal type. A key counts the
unification variables of the goal and of the leaves' types as given, as the
walk's keys do. A leaf whose result is a type variable that no parameter has
('anyResult') fits every goal, so it is left out, unless a program must use
it, or the flag is on and a class constraint reads that variable
('classResult'), as in @fromIntegral@ and @mempty@: a search in the order of
a score can rank such leaves.
-}
holeGoals :: Environment -> Bool -> [(Leaf, Bool)] -> Int -> Type -> TcM (Goals TcM StateKey)
holeGoals environment constrained leaves most goal = do
    root <- liftZonkM (zonkTcType goal)
    rootKey <- keyOf root
    representatives <- liftIO (newIORef (Map.singleton rootKey root))
    let childKey child = do
            zonked <- liftZonkM (zonkTcType child)
            key <- keyOf zonked
            liftIO (modifyIORef' representatives (Map.insertWith (\_ old -> old) key zonked))
            pure key
        transitions deadline key counts = do
            known <- liftIO (Map.lookup key <$> readIORef representatives)
            case known of
                Nothing -> pure (Just [])
                Just goal' ->
                    -- One walker for all the steps on the goal: its variables
                    -- come from the types of every leaf, once.
                    refine
                        deadline
                        (startWalker environment types goal')
                        [(rank, index, k) | (rank, (index, k)) <- zip [0 ..] (fitting (headOf [] goal')), k `elem` counts]
                        []
        -- Step each leaf with its number of children on the walker of the
        -- goal, in the order of the index; no unification stays.
        refine deadline walker tried found = case tried of
            [] -> pure (Just (reverse found))
            (rank, index, k) : rest -> do
                now <- liftIO getMonotonicTimeNSec
                if maybe False (now >=) deadline
                    then pure Nothing
                    else do
                        frozen <- freeze environment walker
                        stepped <- step environment walker (byIndex IntMap.! index) k False
                        children <- traverse (mapM childKey . take k . walkerGoals) stepped
                        restore environment frozen
                        refine deadline walker rest (maybe found (\keys -> Refinement rank index k keys : found) children)
    pure
        Goals
            { goalsLeaves = map (leafName . fst) kept
            , goalsRequired = [index | (index, (_, True)) <- zip [0 ..] kept]
            , goalsRoot = rootKey
            , goalsTransitions = transitions
            }
  where
    kept =
        [ (leaf, required)
        | (leaf, required) <- leaves
        , required || not (anyResult (leafType leaf)) || (constrained && classResult (leafType leaf))
        ]
    byIndex = IntMap.fromList (zip [0 ..] (map fst kept))
    types = map (leafType . fst) leaves
    given = walkerVariables (startWalker environment types goal)
    keyOf typ = stateKey environment given (Walker [] emptyWC [typ])
    byHead =
        Map.fromListWith
            (flip (<>))
            [(top, [(index, k)]) | (index, (leaf, _)) <- zip [0 :: Int ..] kept, (k, top) <- entries most (leafType leaf)]
    -- The leaves with a number of children whose result can fit a goal of a
    -- head: those of an exact head first, then those of a variable result.
    fitting top = case top of
        Any -> concat (Map.elems byHead)
        Exact _ -> Map.findWithDefault [] top byHead <> Map.findWithDefault [] Any byHead

{- | The heads of a leaf's results for each number of children up to a
bound: after @k@ visible arrows of its type, the head of the rest. A leaf
whose rest is a concrete type and not a function takes no more children.
-}
entries :: Int -> Type -> [(Int, Head)]
entries most typ = go 0 rho
  where
    (bound, _, rho) = tcSplitNestedSigmaTys (expandTypeSynonyms typ)
    go k rest
        | k > most = []
        | Just (_, result) <- splitVisibleFunTy_maybe rest = (k, headOf bound rest) : go (k + 1) result
        | otherwise = case headOf bound rest of
            Any -> [(k', Any) | k' <- [k .. most]]
            top -> [(k, top)]

{- | The head of a type: a type constructor (also the arrow), or a rigid
variable, applied or not, is exact; a bound variable (one of the given
list) or a unification variable matches every head.
-}
headOf :: [TyVar] -> Type -> Head
headOf bound typ = case tcSplitTyConApp_maybe typ of
    Just (constructor, _) -> Exact (getKey (getUnique constructor))
    Nothing -> case leftmost typ of
        TyVarTy variable
            | variable `elem` bound || (isTcTyVar variable && isMetaTyVar variable) -> Any
            | otherwise -> Exact (getKey (getUnique variable))
        _ -> Any
  where
    leftmost (AppTy function _) = leftmost function
    leftmost other = other

{- | Whether the result of a type is a type variable that a class constraint
of the type reads, as in @(Integral a, Num b) => a -> b@.
-}
classResult :: Type -> Bool
classResult typ = case result of
    TyVarTy variable -> variable `elemVarSet` tyCoVarsOfTypes theta
    _ -> False
  where
    (_, theta, rho) = tcSplitNestedSigmaTys (expandTypeSynonyms typ)
    (_, result) = tcSplitFunTys rho

{- | Whether the result of a type is a type variable that no parameter has, as
in @a@ and @[Char] -> a@.
-}
anyResult :: Type -> Bool
anyResult typ = case result of
    TyVarTy variable -> variable `elem` bound && not (variable `elemVarSet` tyCoVarsOfTypes parameters)
    _ -> False
  where
    (bound, _, rho) = tcSplitNestedSigmaTys (expandTypeSynonyms typ)
    (scaled, result) = tcSplitFunTys rho
    parameters = map scaledThing scaled
