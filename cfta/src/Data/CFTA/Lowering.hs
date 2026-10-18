{- | Template lowerings: translate the terms of one language version to the
version before it.

A lowering gives each new constructor an expansion: a tree of the earlier
language whose leaves can be the children of the lowered node. Every other
constructor stays as it is. A lowering is a tree homomorphism, so the inverse
image of a tree automaton under it is a tree automaton again ('lift'). This
module handles automata without constraints.
-}
module Data.CFTA.Lowering (
    Expansion (..),
    Lowering,
    ExpansionError (..),
    LoweringError (..),
    mkLowering,
    lower,
    lift,
    checkLowering,
) where

import Control.Monad (forM_, replicateM, unless)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A tree of the earlier language. @Child i@ is the child with index @i@ of the lowered node.
data Expansion symbol
    = Child !Int
    | Apply !symbol ![Expansion symbol]
    deriving (Eq, Show)

-- | The arity and the expansion of each new constructor.
newtype Lowering symbol = Lowering (Map symbol (Int, Expansion symbol))
    deriving (Eq, Show)

-- | A second expansion for a constructor, or an expansion that uses a child that the constructor does not have.
data ExpansionError symbol
    = DuplicateExpansion !symbol
    | ChildOutOfRange !symbol !Int
    deriving (Eq, Show)

-- | An automaton that 'lift' does not handle, or a production that does not lower.
data LoweringError state symbol
    = ConstrainedTransition !state !symbol
    | InvalidLift !(FTA.FTAError state symbol)
    | ArityMismatch !symbol !Int !Int
    | NotLowered !state !symbol ![state]
    deriving (Eq, Show)

-- | Check that each constructor has one expansion, and that each expansion uses only the children of the constructor.
mkLowering :: (Ord symbol) => [(symbol, Int, Expansion symbol)] -> Either (ExpansionError symbol) (Lowering symbol)
mkLowering entries = do
    forM_ entries $ \(symbol, arity, expansion) ->
        forM_ (children expansion) $ \index ->
            unless (0 <= index && index < arity) $ Left $ ChildOutOfRange symbol index
    let table = Map.fromListWith (\_ _ -> Nothing) [(symbol, Just (arity, expansion)) | (symbol, arity, expansion) <- entries]
    case [symbol | (symbol, Nothing) <- Map.toList table] of
        symbol : _ -> Left $ DuplicateExpansion symbol
        [] -> Right $ Lowering $ Map.mapMaybe id table
  where
    children (Child index) = [index]
    children (Apply _ arguments) = concatMap children arguments

{- | Lower a term: lower the children, then put them in the expansion of a new
constructor. 'Nothing' if a new constructor has a different number of children
than its arity.
-}
lower :: (Ord symbol) => Lowering symbol -> Term symbol -> Maybe (Term symbol)
lower lowering@(Lowering expansions) (Term.Node symbol children) = do
    lowered <- traverse (lower lowering) children
    case Map.lookup symbol expansions of
        Nothing -> Just $ Term.Node symbol lowered
        Just (arity, expansion)
            | length lowered == arity -> Just $ expand lowered expansion
            | otherwise -> Nothing
  where
    expand arguments (Child index) = arguments !! index
    expand arguments (Apply inner parts) = Term.Node inner $ map (expand arguments) parts

{- | The terms whose lowering the automaton accepts. The states stay the same.
A transition of a new constructor goes from a state @q@ to children
@q1 ... qk@ when the expansion, with its children at @q1 ... qk@, has a run
from @q@. Transitions of the new constructors in the automaton itself are
removed, because their terms lower to other terms. Every transition must have
no constraint.
-}
lift ::
    (Ord state, Ord symbol) =>
    Lowering symbol -> FTA.PlainFTA state symbol -> Either (LoweringError state symbol) (FTA.PlainFTA state symbol)
lift (Lowering expansions) automaton = do
    forM_ (Map.toList table) $ \(state, transitions) ->
        forM_ transitions $ \transition ->
            unless (FTA.transitionConstraint transition == noConstraint)
                $ Left
                $ ConstrainedTransition state (FTA.transitionSymbol transition)
    first InvalidLift $ FTA.mkFTA (FTA.initialState automaton) $ Map.toList $ Map.unionWith (<>) kept added
  where
    table = FTA.transitionTable automaton
    kept = Map.map (filter $ \transition -> Map.notMember (FTA.transitionSymbol transition) expansions) table
    added =
        Map.fromListWith
            (flip (<>))
            [ (state, [FTA.Transition symbol children noConstraint])
            | (symbol, (arity, expansion)) <- Map.toList expansions
            , children <- replicateM arity $ FTA.states automaton
            , state <- Set.toList $ runs (reverseTable table) children expansion
            ]

{- | Check, for each production of the later grammar, that its terms lower to
terms of the earlier grammar at the same state. A production of a new
constructor must have its arity, and its expansion must have a run from its
state with the children at their states. A production of any other
constructor must be in the earlier grammar. By induction on terms, the check
shows that every term of the later grammar lowers to a term of the earlier
grammar. The two grammars share their states. Constraints are not checked.
-}
checkLowering ::
    (Ord state, Ord symbol) =>
    Lowering symbol ->
    FTA.FTA state symbol constraint ->
    FTA.FTA state symbol constraint ->
    [LoweringError state symbol]
checkLowering (Lowering expansions) earlier later =
    [ failure
    | (state, transitions) <- Map.toList $ FTA.transitionTable later
    , FTA.Transition symbol children _ <- transitions
    , failure <- check state symbol children
    ]
  where
    known = reverseTable $ FTA.transitionTable earlier
    check state symbol children = case Map.lookup symbol expansions of
        Just (arity, expansion)
            | length children /= arity -> [ArityMismatch symbol arity (length children)]
            | Set.member state (runs known children expansion) -> []
            | otherwise -> [NotLowered state symbol children]
        Nothing
            | Set.member state (Map.findWithDefault Set.empty (symbol, children) known) -> []
            | otherwise -> [NotLowered state symbol children]

-- | The states that have each transition, by symbol and children.
reverseTable ::
    (Ord state, Ord symbol) => Map state [FTA.Transition state symbol constraint] -> Map (symbol, [state]) (Set.Set state)
reverseTable table =
    Map.fromListWith
        Set.union
        [ ((FTA.transitionSymbol transition, FTA.transitionChildren transition), Set.singleton state)
        | (state, transitions) <- Map.toList table
        , transition <- transitions
        ]

-- | The states from which an expansion has a run, with its children at the given states.
runs :: (Ord state, Ord symbol) => Map (symbol, [state]) (Set.Set state) -> [state] -> Expansion symbol -> Set.Set state
runs known children = go
  where
    go (Child index) = Set.singleton $ children !! index
    go (Apply symbol parts) =
        Set.unions
            [ Map.findWithDefault Set.empty (symbol, states) known
            | states <- traverse (Set.toList . go) parts
            ]
