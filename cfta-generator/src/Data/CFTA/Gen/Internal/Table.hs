-- | Shared size indexing for ordinary, possibly recursive automata.
module Data.CFTA.Gen.Internal.Table (
    tableIndex,
    tableIndexes,
    tablePosition,
    prefixedTable,
    childStarts,
    minimumSizes,
    unambiguousRows,
    sortedRows,
) where

import Control.Monad (foldM, zipWithM)
import Data.Array (listArray, (!))
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (sortOn, tails)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Index (Size, TransitionIndex (..))
import Data.CFTA.Interned (NodeId (..), canonicalClasses)
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
    withKnotMetadata,
 )
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

{- | Index ordinary transition rows supplied by a graph adapter.

Missing rows accept nothing. Constraint layers must validate their annotations
before supplying ordinary rows. This worker does not interpret constraints.
-}
tableIndex ::
    (Ord state) => state -> Map.Map state [FTA.Transition state symbol ()] -> SizeIndex (Term symbol)
tableIndex initial rows = fst (stateTable rows) initial

{- | The size index of each state of the rows, as 'tableIndex' gives it.
Apply the function to the rows once: the states then share one table.
-}
tableIndexes ::
    (Ord state) => Map.Map state [FTA.Transition state symbol ()] -> state -> SizeIndex (Term symbol)
tableIndexes rows = fst (stateTable rows)

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
    state -> Map.Map state [FTA.Transition state symbol ()] -> Term symbol -> Maybe SizedRank
tablePosition initial rows = Map.lookup initial . termPositions rows (stateTable rows)

-- | The size and position of a term in each state that accepts it, from the table of the rows.
termPositions ::
    (Ord state, Ord symbol) =>
    Map.Map state [FTA.Transition state symbol ()] ->
    ( state -> SizeIndex (Term symbol)
    , state -> [(FTA.Transition state symbol (), NonEmpty (SizeIndex ([Term symbol] -> Term symbol)))]
    ) ->
    Term symbol ->
    Map.Map state SizedRank
termPositions rows (indexOf, prefixesOf) = positionsOf
  where
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
    positionsOf (Term.Node symbol children) =
        Map.fromList
            [ (state, SizedRank size (choicePosition indexes (ChoiceIndex branch) size position))
            | (state, TransitionIndex branch, transition, prefixes, indexes) <-
                toList $ Map.findWithDefault Empty (symbol, length children) candidates
            , Just childPositions <- [zipWithM Map.lookup (FTA.transitionChildren transition) childMaps]
            , let SizedRank size position =
                    foldl' addChild (SizedRank 1 0) $ zip3 (NonEmpty.toList prefixes) (FTA.transitionChildren transition) childPositions
            ]
      where
        childMaps = map positionsOf children

        addChild built (prefix, child, childPosition) =
            productPosition prefix (indexOf child) built childPosition

{- | The size index of each state, and the transitions of each state with the
indexes of their child prefixes.

The first prefix index holds the symbol alone. Each next prefix index adds one
child, and the last one holds the terms of the transition. Each state has one
index, which recursive references to the state share.
-}
stateTable ::
    (Ord state) =>
    Map.Map state [FTA.Transition state symbol ()] ->
    ( state -> SizeIndex (Term symbol)
    , state -> [(FTA.Transition state symbol (), NonEmpty (SizeIndex ([Term symbol] -> Term symbol)))]
    )
stateTable rows = (indexOf, prefixesOf)
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

-- | The index of a transition before its children: the symbol, with its pay.
seed :: FTA.Transition state symbol () -> SizeIndex ([Term symbol] -> Term symbol)
seed transition = payIndex $ constantIndex $ Term.Node $ FTA.transitionSymbol transition

-- | The index of a transition with one more child.
consumeChild ::
    SizeIndex ([Term symbol] -> Term symbol) -> SizeIndex (Term symbol) -> SizeIndex ([Term symbol] -> Term symbol)
consumeChild built = productIndex (mapIndex prepend built)
  where
    prepend build term arguments = build (term : arguments)

{- | The size index of the terms of a state whose preorder starts with a
prefix, and the size and position of each such term in that index.

A token is a symbol and its number of children. The index of a prefix is a
choice over the transitions of the state whose token is the first token of the
prefix, in their order. Each child of such a transition has the index of its
part of the prefix ('childStarts'), or the index of its state when the prefix
ends before the child. These are the combinators of 'tableIndex', and a part of
a product or a choice keeps the order of the whole. So the order of the terms
is the order of 'tableIndex', restricted to the terms with the prefix. The
index is empty when tokens remain after the first term of the prefix.

The rows must be unambiguous, as for 'tablePosition'. Apply the function to
the rows once: the prefixes then share one table of the states.
-}
prefixedTable ::
    (Ord state, Ord symbol) =>
    Map.Map state [FTA.Transition state symbol ()] ->
    state ->
    [(symbol, Int)] ->
    (SizeIndex (Term symbol), Term symbol -> Maybe SizedRank)
prefixedTable rows = table
  where
    stateIndexes@(indexOf, _) = stateTable rows
    positionsOf = termPositions rows stateIndexes
    table initial prefix
        | maybe False (/= size) end = (choiceIndex [], const Nothing)
        | otherwise = (indexAt initial 0, positionAt initial 0)
      where
        size = length prefix
        tokens = listArray (0, size - 1) prefix
        (starts, end) = childStarts prefix
        -- The transitions of a state with the token at a position, each with
        -- the indexes of its child prefixes, as 'stateTable' gives them.
        nodes =
            LazyMap.fromList
                [ ( (state, position)
                  , [ ( transition
                      , NonEmpty.scanl consumeChild (seed transition) (zipWith indexAt (FTA.transitionChildren transition) (starts position))
                      )
                    | transition <- Map.findWithDefault [] state rows
                    , (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition) == tokens ! position
                    ]
                  )
                | state <- Map.keys rows
                , position <- [0 .. size - 1]
                ]
        branchIndexes branches = [mapIndex ($ []) (NonEmpty.last prefixes) | (_, prefixes) <- branches]
        indexAt state position
            | position >= size = indexOf state
            | otherwise = choiceIndex $ branchIndexes $ nodes LazyMap.! (state, position)
        positionAt state position term
            | position >= size = Map.lookup state $ positionsOf term
            | Term.Node symbol children <- term
            , (symbol, length children) == tokens ! position =
                listToMaybe
                    [ SizedRank termSize (choicePosition (branchIndexes branches) (ChoiceIndex branch) termSize rank)
                    | (branch, (transition, prefixes)) <- zip [0 ..] branches
                    , let childStates = FTA.transitionChildren transition
                    , Just childPositions <- [sequence $ zipWith3 positionAt childStates (starts position) children]
                    , let SizedRank termSize rank =
                            foldl'
                                addChild
                                (SizedRank 1 0)
                                (zip3 (NonEmpty.toList prefixes) (zipWith indexAt childStates $ starts position) childPositions)
                    ]
            | otherwise = Nothing
          where
            branches = nodes LazyMap.! (state, position)
        addChild built (prefixIndex, childIndex, childPosition) = productPosition prefixIndex childIndex built childPosition

{- | The parts of a preorder prefix. For each position of a token, the position
where the prefix of each child of the token starts, in order. A child that the
prefix does not reach starts at the end of the prefix. Also the end of the
first term: the position after its last token, or 'Nothing' when the prefix
ends inside it.
-}
childStarts :: [(symbol, Int)] -> (Int -> [Int], Maybe Int)
childStarts prefix = (starts, if size == 0 then Nothing else ends ! 0)
  where
    size = length prefix
    arities = listArray (0, size - 1) (map snd prefix)
    ends = listArray (0, size - 1) [endOf position | position <- [0 .. size - 1]]
    -- The position after the term that starts at a position.
    endOf position = foldM (\next _ -> if next < size then ends ! next else Nothing) (position + 1) [1 .. arities ! position]
    starts position = take (arities ! position) $ iterate after (position + 1)
    after start
        | start < size, Just end <- ends ! start = end
        | otherwise = size

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

{- | Whether each term has at most one run in the rows. Bottom-up
deterministic rows are unambiguous; otherwise the check builds a product.

The synchronous product accepts the common terms of each pair of states.
Two alternatives overlap when every pair of child states is productive.
-}
unambiguousRows :: (Ord state, Ord symbol) => Map.Map state [FTA.Transition state symbol ()] -> Bool
unambiguousRows rows =
    bottomUpDeterministic
        || not
            ( or
                [ FTA.transitionSymbol left == FTA.transitionSymbol right
                    && length (FTA.transitionChildren left) == length (FTA.transitionChildren right)
                    && all (`Map.member` productive) (zip (FTA.transitionChildren left) (FTA.transitionChildren right))
                | alternatives <- Map.elems rows
                , left : rest <- tails alternatives
                , right <- rest
                ]
            )
  where
    -- No two transitions with the same symbol and the same child states, as
    -- in an e-graph: then each term reaches at most one state, by induction on
    -- the term, so each term has at most one run. A set of transition keys
    -- checks this before the product of each pair of states.
    bottomUpDeterministic = length keys == Set.size (Set.fromList keys)
    keys =
        [ (FTA.transitionSymbol transition, FTA.transitionChildren transition)
        | transitions <- Map.elems rows
        , transition <- transitions
        ]
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

{- | The transitions of each state in the order of the count table of the
cyclic import: by arity, symbol, and the canonical classes of their children.

The classes are those of the whole graph, as in the import. A trim would
remove the transitions with a child that accepts nothing, and that can change
the order of the classes of the other states.
-}
sortedRows ::
    (Ord state, Ord symbol) => FTA.FTA state symbol constraint -> Map.Map state [FTA.Transition state symbol constraint]
sortedRows automaton = Map.map (sortOn rowKey) (FTA.transitionTable automaton)
  where
    -- Each state has a number, so that the canonical classes can refine the rows.
    numbers = Map.fromList $ zip (Map.keys $ FTA.transitionTable automaton) [0 ..]
    number state = numbers Map.! state
    classes =
        canonicalClasses $
            IntMap.fromList
                [ ( number state
                  , [ ((length children, FTA.transitionSymbol transition), map (NodeId . number) children)
                    | transition <- transitions
                    , let children = FTA.transitionChildren transition
                    ]
                  )
                | (state, transitions) <- Map.toList (FTA.transitionTable automaton)
                ]
    rowKey transition =
        ( length $ FTA.transitionChildren transition
        , FTA.transitionSymbol transition
        , [classes IntMap.! number child | child <- FTA.transitionChildren transition]
        )
