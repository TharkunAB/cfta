-- | Shared size indexing for ordinary, possibly recursive automata.
module Data.CFTA.Gen.Internal.Table (
    LeafSource (..),
    tableIndex,
    tableIndexes,
    tablePosition,
    minimumSizes,
    unambiguousRows,
) where

import Control.Monad (zipWithM)
import Data.Foldable (toList)
import Data.List (tails)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence

import qualified Data.CFTA as FTA
import Data.CFTA.Index (Cardinality, ClassRank (..), Rank (..), Size, TransitionIndex (..))
import Data.CFTA.Ranked.Internal.Decoder (Plan (PlanSelect))
import Data.CFTA.Ranked.Internal.Size (
    ChoiceIndex (..),
    MinimumSize (..),
    SizeIndex,
    SizedRank (..),
    choiceIndex,
    choicePosition,
    closedProbe,
    constantIndex,
    mapIndex,
    payIndex,
    productIndex,
    productPosition,
    sizeIndex,
    withKnotMetadata,
 )
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

{- | A nullary symbol that stands for many leaves.

The symbol is one transition of the rows. Its leaves are the terms of 'leafTerm'
for the ranks below 'leafCount'. Each leaf has size one. 'leafRank' is the
inverse of 'leafTerm': it gives 'Nothing' for a term that the source does not
hold. The source does not list its leaves.
-}
data LeafSource symbol = LeafSource
    { leafCount :: !Cardinality
    , leafTerm :: Rank -> Term symbol
    , leafRank :: Term symbol -> Maybe Rank
    }

{- | Index ordinary transition rows supplied by a graph adapter.

Missing rows accept nothing. Constraint layers must validate their annotations
before supplying ordinary rows. This worker does not interpret constraints.
-}
tableIndex ::
    (Ord state) =>
    (symbol -> Maybe (LeafSource symbol)) ->
    state ->
    Map.Map state [FTA.Transition state symbol ()] ->
    SizeIndex (Term symbol)
tableIndex leafOf initial rows = fst (stateTable leafOf rows) initial

{- | The size index of each state of the rows, as 'tableIndex' gives it.
Apply the function to the rows once: the states then share one table.
-}
tableIndexes ::
    (Ord state) =>
    (symbol -> Maybe (LeafSource symbol)) ->
    Map.Map state [FTA.Transition state symbol ()] ->
    state ->
    SizeIndex (Term symbol)
tableIndexes leafOf rows = fst (stateTable leafOf rows)

{- | Find the size class and the position in it of a term that the initial
state accepts, as 'tableIndex' selects the term.

The size is the number of term nodes. 'Nothing' means that the initial state
does not accept the term. The rows must be unambiguous: one run at most
accepts each term. The positions are found bottom-up, once for each subterm
and each state that accepts it, so no subterm is ranked again. Apply the
function to the rows once: each term then uses the same counts.
-}
tablePosition ::
    (Ord state, Ord symbol) =>
    (symbol -> Maybe (LeafSource symbol)) ->
    state ->
    Map.Map state [FTA.Transition state symbol ()] ->
    Term symbol ->
    Maybe SizedRank
tablePosition leafOf initial rows = Map.lookup initial . positionsOf
  where
    (indexOf, prefixesOf) = stateTable leafOf rows
    -- The transitions of leaf sources, to find the source that holds a leaf.
    leafCandidates =
        [ (state, branch, source, indexes)
        | state <- Map.keys rows
        , let indexes = map (NonEmpty.last . snd) $ prefixesOf state
        , (branch, (transition, _)) <- zip [0 :: TransitionIndex ..] $ prefixesOf state
        , null (FTA.transitionChildren transition)
        , Just source <- [leafOf (FTA.transitionSymbol transition)]
        ]
    -- The candidates by symbol and arity. The candidates of a state share
    -- its transition indexes, so they are built once for each state.
    -- TODO: The candidates of a key are a Seq that grows in order; lists that
    -- grow with flip (<>) are the alternative. With the series of commits that
    -- made them Seqs, rank-of-term on a datatype import (TablePositionProbe,
    -- 2026-10-09) took 8% to 13% more wall-clock at sizes 64 and 128, beyond a
    -- noise of 5% to 7%, while it ran 0.08% fewer instructions. The cause is
    -- not known; this code is one of the few changes on that path.
    candidates =
        Map.fromListWith
            (flip (<>))
            [ ( (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
              , Sequence.singleton (state, branch, transition, prefixes, indexes)
              )
            | state <- Map.keys rows
            , let indexes = map (NonEmpty.last . snd) $ prefixesOf state
            , (branch, (transition, prefixes)) <- zip [0 :: TransitionIndex ..] $ prefixesOf state
            ]
    -- The size and position of a term in each state that accepts it. The
    -- index of a state is a choice over its transitions, so the index of a
    -- transition is its choice index.
    positionsOf term@(Term.Node symbol children)
        | null children && not (null leafCandidates) = ordinary <> leaves
        | otherwise = ordinary
      where
        childMaps = map positionsOf children

        addChild built (prefix, child, childPosition) =
            productPosition prefix (indexOf child) built childPosition

        leaves =
            Map.fromList
                [ (state, SizedRank 1 (choicePosition indexes (ChoiceIndex branch) 1 (ClassRank position)))
                | (state, TransitionIndex branch, source, indexes) <- leafCandidates
                , Just (Rank position) <- [leafRank source term]
                ]

        ordinary =
            Map.fromList
                [ (state, SizedRank size (choicePosition indexes (ChoiceIndex branch) size position))
                | (state, TransitionIndex branch, transition, prefixes, indexes) <-
                    toList $ Map.findWithDefault Empty (symbol, length children) candidates
                , Just childPositions <- [zipWithM Map.lookup (FTA.transitionChildren transition) childMaps]
                , let SizedRank size position =
                        foldl' addChild (SizedRank 1 0) $ zip3 (NonEmpty.toList prefixes) (FTA.transitionChildren transition) childPositions
                ]

{- | The size index of each state, and the transitions of each state with the
indexes of their child prefixes.

The first prefix index holds the symbol alone. Each next prefix index adds one
child, and the last one holds the terms of the transition. Each state has one
index, which recursive references to the state share.
-}
stateTable ::
    (Ord state) =>
    (symbol -> Maybe (LeafSource symbol)) ->
    Map.Map state [FTA.Transition state symbol ()] ->
    ( state -> SizeIndex (Term symbol)
    , state -> [(FTA.Transition state symbol (), NonEmpty (SizeIndex ([Term symbol] -> Term symbol)))]
    )
stateTable leafOf rows = (indexOf, prefixesOf)
  where
    minima = minimumSizes rows
    prefixTable = LazyMap.map (map $ \transition -> (transition, childPrefixes transition)) rows
      where
        childPrefixes transition =
            NonEmpty.scanl consumeChild (seed transition) (map indexOf $ FTA.transitionChildren transition)
    -- Sampling reads this index. It is built directly, not as the last child
    -- prefix, because an index from the prefix list made each sample slower
    -- (about 1% more instructions in the sampling benchmarks).
    indexTable = LazyMap.mapWithKey stateIndex rows
      where
        stateIndex state transitions =
            -- The rows are closed, so they reach no probe of an enclosing definition.
            withKnotMetadata
                (maybe NoFiniteMember MinimumSize $ Map.lookup state minima)
                (closedProbe NoFiniteMember)
                (choiceIndex $ map transitionIndex transitions)

        transitionIndex transition =
            mapIndex ($ []) $
                foldl' consumeChild (seed transition) (map indexOf $ FTA.transitionChildren transition)
    indexOf state
        | Map.member state minima = Map.findWithDefault emptyIndex state indexTable
        | otherwise = emptyIndex
    prefixesOf state
        | Map.member state minima = Map.findWithDefault [] state prefixTable
        | otherwise = []
    emptyIndex = choiceIndex []
    -- The index of a transition before its children: the symbol, with its pay.
    -- A leaf source gives its leaves, each of size one.
    seed transition = case leafOf (FTA.transitionSymbol transition) of
        Just source
            | null (FTA.transitionChildren transition) ->
                mapIndex const $ sizeIndex $ PlanSelect (leafCount source) (leafTerm source)
        _ -> payIndex $ constantIndex $ Term.Node $ FTA.transitionSymbol transition
    consumeChild built child = productIndex (mapIndex prepend built) child
      where
        prepend build term arguments = build (term : arguments)

{- | Find the least finite term size of each productive state.

Start with no productive states and solve the least fixed point. A cycle with
no finite base remains absent. This keeps an empty recursive index finite.
-}
minimumSizes :: (Ord state) => Map.Map state [FTA.Transition state symbol constraint] -> Map.Map state Size
minimumSizes rows = converge Map.empty
  where
    converge current =
        let next = Map.foldrWithKey addMinimum current rows
         in if next == current then current else converge next
      where
        addMinimum state transitions known =
            case mapMaybe (transitionMinimum known) transitions of
                [] -> known
                sizes -> Map.insertWith min state (minimum sizes) known
    transitionMinimum known transition =
        (1 +) . sum <$> traverse (`Map.lookup` known) (FTA.transitionChildren transition)

{- | Whether each term has at most one run in the rows.

The synchronous product accepts the common terms of each pair of states.
Two alternatives overlap when every pair of child states is productive.
-}
unambiguousRows :: (Ord state, Eq symbol) => Map.Map state [FTA.Transition state symbol ()] -> Bool
unambiguousRows rows =
    not $
        or
            [ FTA.transitionSymbol left == FTA.transitionSymbol right
                && length (FTA.transitionChildren left) == length (FTA.transitionChildren right)
                && all (`Map.member` productive) (zip (FTA.transitionChildren left) (FTA.transitionChildren right))
            | alternatives <- Map.elems rows
            , left : rest <- tails alternatives
            , right <- rest
            ]
  where
    productive = minimumSizes products
    products =
        Map.fromList
            [ ( (leftState, rightState)
              , [ FTA.Transition (FTA.transitionSymbol left) (zip (FTA.transitionChildren left) (FTA.transitionChildren right)) ()
                | left <- leftRows
                , right <- rightRows
                , FTA.transitionSymbol left == FTA.transitionSymbol right
                , length (FTA.transitionChildren left) == length (FTA.transitionChildren right)
                ]
              )
            | (leftState, leftRows) <- Map.toList rows
            , (rightState, rightRows) <- Map.toList rows
            ]
