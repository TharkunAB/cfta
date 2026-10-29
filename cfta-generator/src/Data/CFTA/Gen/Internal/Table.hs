-- | Shared size indexing for ordinary, possibly recursive automata.
module Data.CFTA.Gen.Internal.Table (
    EqualChildren,
    LeafSource (..),
    tableIndex,
    tableIndexes,
    tablePosition,
    prefixedTable,
    childStarts,
    childGroups,
    equalChildren,
    minimumSizes,
    unambiguousRows,
    deterministicRows,
    countingRows,
    plainCountingRows,
    deterministicCountingRows,
    intersectionCountingRows,
    sortedRows,
) where

import Control.Monad (foldM, zipWithM)
import Data.Array (listArray, (!))
import Data.Either (fromRight)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (inits, partition, sort, sortOn, tails)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalities, residual)
import Data.CFTA.Equality.Constraint (EqConstraints, subsumptionOrderedEclasses, unPathEClass)
import Data.CFTA.Index (Arity (..), Cardinality, ClassRank (..), Rank (..), Size, TransitionIndex (..), childIndexes)
import Data.CFTA.Interned (NodeId (..), canonicalClasses)
import Data.CFTA.Path (ChildIndex (..), unPath)
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
    scaleIndex,
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

{- | The classes of equal children of a transition: in each class, the child
positions whose subterms are equal. A class has two positions or more, its
positions are in ascending order, and the classes are in the order of their
first positions. The table reads the child at the first position of a class,
and its term fills each position of the class, so its size counts once for
each position. A transition without classes has the empty list.
-}
type EqualChildren = [[ChildIndex]]

{- | Index ordinary transition rows supplied by a graph adapter.

Missing rows accept nothing. Constraint layers must validate their annotations
before supplying ordinary rows. This worker does not interpret constraints;
it reads only the classes of equal children.
-}
tableIndex ::
    (Ord state) =>
    (symbol -> Maybe (LeafSource symbol)) ->
    state ->
    Map.Map state [FTA.Transition state symbol EqualChildren] ->
    SizeIndex (Term symbol)
tableIndex leafOf initial rows = fst (stateTable leafOf rows) initial

{- | The size index of each state of the rows, as 'tableIndex' gives it.
Apply the function to the rows once: the states then share one table.
-}
tableIndexes ::
    (Ord state) =>
    (symbol -> Maybe (LeafSource symbol)) ->
    Map.Map state [FTA.Transition state symbol EqualChildren] ->
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
    Map.Map state [FTA.Transition state symbol EqualChildren] ->
    Term symbol ->
    Maybe SizedRank
tablePosition leafOf initial rows = Map.lookup initial . termPositions leafOf rows (stateTable leafOf rows)

-- | The size and position of a term in each state that accepts it, from the table of the rows.
termPositions ::
    (Ord state, Ord symbol) =>
    (symbol -> Maybe (LeafSource symbol)) ->
    Map.Map state [FTA.Transition state symbol EqualChildren] ->
    ( state -> SizeIndex (Term symbol)
    , state -> [(FTA.Transition state symbol EqualChildren, NonEmpty (SizeIndex ([Term symbol] -> Term symbol)))]
    ) ->
    Term symbol ->
    Map.Map state SizedRank
termPositions leafOf rows (indexOf, prefixesOf) = positionsOf
  where
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

        -- The size and position of the term in a transition. The subterms of
        -- a class of equal children must be equal, and the table reads the
        -- first child of each group.
        transitionPosition transition prefixes childPositions = case FTA.transitionConstraint transition of
            [] ->
                Just
                    $ foldl' addChild (SizedRank 1 0)
                    $ zip3 (NonEmpty.toList prefixes) (map indexOf $ FTA.transitionChildren transition) childPositions
            classes
                | and [children !! other == children !! first | ChildIndex first : rest <- classes, ChildIndex other <- rest] ->
                    Just
                        $ foldl' addChild (SizedRank 1 0)
                        $ zip3
                            (NonEmpty.toList prefixes)
                            [scaled factor $ indexOf (FTA.transitionChildren transition !! first) | (factor, first) <- leaders]
                            [scaledRank factor (childPositions !! first) | (factor, first) <- leaders]
                | otherwise -> Nothing
              where
                leaders = [(length group, first) | group@(ChildIndex first : _) <- childGroupsOf (length children) classes]

        addChild built (prefix, index, childPosition) =
            productPosition prefix index built childPosition
        scaledRank factor (SizedRank size rank) = SizedRank (fromIntegral factor * size) rank

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
                , Just (SizedRank size position) <- [transitionPosition transition prefixes childPositions]
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
    Map.Map state [FTA.Transition state symbol EqualChildren] ->
    ( state -> SizeIndex (Term symbol)
    , state -> [(FTA.Transition state symbol EqualChildren, NonEmpty (SizeIndex ([Term symbol] -> Term symbol)))]
    )
stateTable leafOf rows = (indexOf, prefixesOf)
  where
    minima = minimumSizes rows
    prefixTable = LazyMap.map (map $ \transition -> (transition, childPrefixes transition)) rows
      where
        childPrefixes transition =
            NonEmpty.scanl consumeChild (seed leafOf transition) (childIndexesOf transition)
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
                foldl' consumeChild (seed leafOf transition) (childIndexesOf transition)
    -- The indexes of the children that the table reads. The first child of a
    -- class of equal children fills each position of the class.
    childIndexesOf transition = case FTA.transitionConstraint transition of
        [] -> map indexOf children
        classes ->
            [ scaled (length group) $ indexOf (children !! first)
            | group@(ChildIndex first : _) <- childGroupsOf (length children) classes
            ]
      where
        children = FTA.transitionChildren transition
    indexOf state
        | Map.member state minima = Map.findWithDefault emptyIndex state indexTable
        | otherwise = emptyIndex
    prefixesOf state
        | Map.member state minima = Map.findWithDefault [] state prefixTable
        | otherwise = []
    emptyIndex = choiceIndex []

{- | The index of a transition before its children: the symbol, with its pay.
A leaf source gives its leaves, each of size one. The term of a class of equal
children fills each position of the class.
-}
seed ::
    (symbol -> Maybe (LeafSource symbol)) ->
    FTA.Transition state symbol EqualChildren ->
    SizeIndex ([Term symbol] -> Term symbol)
seed leafOf transition = case leafOf symbol of
    Just source
        | null (FTA.transitionChildren transition) ->
            mapIndex const $ sizeIndex $ PlanSelect (leafCount source) (leafTerm source)
    _ -> payIndex $ constantIndex $ case FTA.transitionConstraint transition of
        [] -> Term.Node symbol
        classes ->
            let groups = childGroupsOf (length $ FTA.transitionChildren transition) classes
             in \terms ->
                    Term.Node symbol
                        $ IntMap.elems
                        $ IntMap.fromList [(position, term) | (group, term) <- zip groups terms, ChildIndex position <- group]
  where
    symbol = FTA.transitionSymbol transition

-- | An index whose members fill a number of positions: their sizes are multiplied by it.
scaled :: Int -> SizeIndex a -> SizeIndex a
scaled 1 index = index
scaled factor index = scaleIndex factor index

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

The rows must be unambiguous, as for 'tablePosition', and they have no
classes of equal children. Apply the function to the rows once: the prefixes
then share one table of the states.
-}
prefixedTable ::
    (Ord state, Ord symbol) =>
    Map.Map state [FTA.Transition state symbol ()] ->
    state ->
    [(symbol, Int)] ->
    (SizeIndex (Term symbol), Term symbol -> Maybe SizedRank)
prefixedTable plainRows = table
  where
    -- The completions use no leaf source.
    rows = Map.map (map ([] <$)) plainRows
    stateIndexes@(indexOf, _) = stateTable (const Nothing) rows
    positionsOf = termPositions (const Nothing) rows stateIndexes
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
                      , NonEmpty.scanl
                            consumeChild
                            (seed (const Nothing) transition)
                            (zipWith indexAt (FTA.transitionChildren transition) (starts position))
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

-- | Partition direct child positions into equality classes in child order.
childGroups :: Arity -> EqConstraints -> Maybe [[ChildIndex]]
childGroups arity constraints = do
    classes <- subsumptionOrderedEclasses constraints
    positions <- traverse (traverse childIndex . Set.toAscList . unPathEClass) classes
    pure $ joinGroups (map pure (childIndexes arity)) positions
  where
    childIndex target = case unPath target of
        [index] | index >= 0 && index < ChildIndex (fromEnum arity) -> Just index
        _ -> Nothing

{- | Join the groups of child positions that share a position with a class,
for each class. The groups are in the order of their first positions.
-}
joinGroups :: [[ChildIndex]] -> [[ChildIndex]] -> [[ChildIndex]]
joinGroups = foldl' merge
  where
    merge groups [] = groups
    merge groups positions =
        let (equal, other) = partition (any (`elem` positions)) groups
         in sortOn (take 1) (concat equal : other)

-- | The groups of child positions with two positions or more.
classesOf :: [[ChildIndex]] -> EqualChildren
classesOf groups = [sort group | group@(_ : _ : _) <- groups]

{- | The child positions of a node with a number of children in groups: each
class of equal children, and each other position alone, in the order of their
first positions.
-}
childGroupsOf :: Int -> EqualChildren -> [[ChildIndex]]
childGroupsOf arity = joinGroups (map pure $ childIndexes $ Arity arity)

{- | The classes of equal children of a transition whose constraint is
equalities between direct children: the constraint has no guard beyond
positive equalities, and each path of an equality is one child position.
'Nothing' for another constraint, and for contradictory equalities.
-}
equalChildren :: FTA.Transition state symbol Constraint -> Maybe EqualChildren
equalChildren transition
    | residual constraint = Nothing
    | otherwise = classesOf <$> childGroups (Arity $ length $ FTA.transitionChildren transition) (equalities constraint)
  where
    constraint = FTA.transitionConstraint transition

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
The key has no constraints. Transitions with the same key keep their order
in the row.

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

{- | The rows of the bottom-up deterministic automaton of the rows, and a root
for each state. A deterministic state is a set of states: the states that
accept one term. So each term has one deterministic state, and the
deterministic rows are unambiguous. The root of a state, 'Left', has the
transitions of each deterministic state that holds it; these accept distinct
terms, so the root accepts the terms of the state, each once. A deterministic
state is 'Right'. 'Nothing' when there are more deterministic states than the
given number: the subset construction can grow exponentially.
-}
deterministicRows ::
    (Ord state, Ord symbol) =>
    Int ->
    Map.Map state [FTA.Transition state symbol ()] ->
    Maybe (Map.Map (Either state (Set.Set state)) [FTA.Transition (Either state (Set.Set state)) symbol ()])
deterministicRows limit rows = go Set.empty Map.empty Map.empty (step Set.empty Map.empty Set.empty)
  where
    -- The transitions of each token, with the state that each one leaves.
    byToken =
        Map.fromListWith
            (flip (<>))
            [ ((FTA.transitionSymbol transition, length $ FTA.transitionChildren transition), [(state, transition)])
            | (state, transitions) <- Map.toList rows
            , transition <- transitions
            ]
    -- Each round reads only the tuples of sets with a set that the round
    -- before found, as a semi-naive fixed point does, so it reads each tuple
    -- once. The holders of a state are the known sets that hold it.
    go known holders table found
        | Set.size known' > limit = Nothing
        | Set.null fresh = Just $ Map.fromList $ roots <> sets
        | otherwise = go known' holders' table' (step fresh holders' known')
      where
        table' = Map.unionWith (<>) table found
        fresh = Map.keysSet found `Set.difference` known
        known' = known <> fresh
        holders' =
            Map.unionWith (<>) holders $ Map.fromListWith (<>) [(state, [set]) | set <- Set.toList fresh, state <- Set.toList set]
        sets = [(Right set, map (withChildren Right) transitions) | (set, transitions) <- Map.toList table']
        roots =
            [ ( Left state
              , [ withChildren Right transition | (set, transitions) <- Map.toList table', Set.member state set, transition <- transitions
                ]
              )
            | state <- Map.keys rows
            ]
    -- The deterministic transitions of the tuples that hold a fresh set.
    step fresh holders known =
        Map.fromListWith
            (flip (<>))
            [ (target, [FTA.Transition symbol children ()])
            | ((symbol, _), members) <- Map.toList byToken
            , children <- Set.toList $ Set.fromList $ concat [tuples (FTA.transitionChildren transition) | (_, transition) <- members]
            , let target =
                    Set.fromList
                        [state | (state, transition) <- members, and (zipWith Set.member (FTA.transitionChildren transition) children)]
            ]
      where
        -- The tuples with the first fresh set at each position: older sets before it, any known set after it.
        tuples [] = [[] | Set.null known]
        tuples children =
            [ before <> [set] <> after
            | (earlier, child : later) <- zip (inits children) (tails children)
            , before <- mapM (filter (`Set.notMember` fresh) . holding) earlier
            , set <- filter (`Set.member` fresh) $ holding child
            , after <- mapM holding later
            ]
        holding state = Map.findWithDefault [] state holders
    withChildren wrap transition = transition{FTA.transitionChildren = map wrap $ FTA.transitionChildren transition}

{- | The rows of the count table of an automaton without constraints, with
the row of each state at 'Left', for the queries of the initial state.
When the rows that the initial state reaches are unambiguous, these are the
rows of the automaton in the order of 'sortedRows'. Otherwise they are the
deterministic rows of all the rows ('deterministicRows'), in the order of
'sortedRows' of the deterministic automaton. All the rows, not only the
reached ones, give the order, as in 'sortedRows', so the order of the terms
of a state does not depend on the initial state. 'Nothing' when the
deterministic automaton has more than 'countingLimit' states.
-}
countingRows ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol () ->
    Maybe (Map.Map (Either state (Set.Set state)) [FTA.Transition (Either state (Set.Set state)) symbol ()])
countingRows automaton
    | unambiguousRows $ FTA.transitionTable $ FTA.trim automaton = Just $ plainCountingRows automaton
    | otherwise = deterministicCountingRows automaton

-- | The rows of the automaton in the order of 'sortedRows', with the row of each state at 'Left'.
plainCountingRows ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol () ->
    Map.Map (Either state (Set.Set state)) [FTA.Transition (Either state (Set.Set state)) symbol ()]
plainCountingRows automaton = Map.mapKeysMonotonic Left $ Map.map (map withLeftChildren) $ sortedRows automaton
  where
    withLeftChildren transition = transition{FTA.transitionChildren = map Left $ FTA.transitionChildren transition}

-- | The deterministic rows of all the rows of the automaton, in the order of 'sortedRows', within 'countingLimit'.
deterministicCountingRows ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol () ->
    Maybe (Map.Map (Either state (Set.Set state)) [FTA.Transition (Either state (Set.Set state)) symbol ()])
deterministicCountingRows automaton = do
    determinized <- deterministicRows countingLimit $ FTA.transitionTable automaton
    pure
        $ sortedRows
        $ fromRight (error "countingRows: the deterministic rows are a valid automaton")
        $ FTA.mkFTA (Left $ FTA.initialState automaton) (Map.toList determinized)

{- | The rows of the count table of the intersections of states, from the rows
that an initial state reaches, in the order of 'sortedRows'. Each constraint
must be equalities between direct children ('equalChildren').

A key is a set of states, and it accepts the terms that each of its states
accepts. The key of one state accepts the terms of the state. The row of a key
has a transition for each tuple of transitions with one token, one transition
of each state of the key. The classes of equal children of the transition join
the classes of the tuple. The child of the transition at a position is the key
of the child states of the tuple at each position of its group, so a class of
equal children has one key. The rows start at the key of the initial state.

The rows must be unambiguous without their constraints, as for
'tablePosition': then a term has at most one run from a key, made of one run
from each of its states. The canonical classes of 'sortedRows' read the classes
of equal children of a transition with its symbol. 'Nothing' when a
constraint is not equalities between direct children, or when there are more
than 'countingLimit' keys, or more than 'countingLimit' transitions of one key:
the tuples of a key can grow exponentially with its states.
-}
intersectionCountingRows ::
    (Ord state, Ord symbol) =>
    Map.Map state [FTA.Transition state symbol Constraint] ->
    state ->
    Maybe (Map.Map (Set.Set state) [FTA.Transition (Set.Set state) symbol EqualChildren])
intersectionCountingRows rows initial = do
    classified <- traverse (traverse $ \transition -> (<$ transition) <$> equalChildren transition) rows
    table <- explore classified Map.empty [Set.singleton initial]
    pure
        $ Map.map (map $ \transition -> transition{FTA.transitionSymbol = fst $ FTA.transitionSymbol transition})
        $ sortedRows
        $ fromRight (error "intersectionCountingRows: the rows of the keys are a valid automaton")
        $ FTA.mkFTA (Set.singleton initial) [(key, map labelled transitions) | (key, transitions) <- Map.toList table]
  where
    labelled transition = transition{FTA.transitionSymbol = (FTA.transitionSymbol transition, FTA.transitionConstraint transition)}
    explore _ table [] = Just table
    explore classified table (key : pending)
        | Map.member key table = explore classified table pending
        | Map.size table >= countingLimit || length row > countingLimit = Nothing
        | otherwise = explore classified (Map.insert key row table) (concatMap FTA.transitionChildren row <> pending)
      where
        row = take (countingLimit + 1) $ case [Map.findWithDefault [] state classified | state <- Set.toList key] of
            first : others ->
                [ intersection transition tuple
                | transition <- first
                , tuple <- mapM (filter $ sameToken transition) others
                ]
            [] -> []
    sameToken left right =
        FTA.transitionSymbol left == FTA.transitionSymbol right
            && length (FTA.transitionChildren left) == length (FTA.transitionChildren right)
    -- The transition of a key from a tuple of transitions with one token.
    intersection transition others = FTA.Transition (FTA.transitionSymbol transition) children (classesOf groups)
      where
        tuple = transition : others
        groups = childGroupsOf (length $ FTA.transitionChildren transition) (concatMap FTA.transitionConstraint tuple)
        children =
            IntMap.elems $
                IntMap.fromList
                    [ (position, key)
                    | group <- groups
                    , let key = Set.fromList [FTA.transitionChildren member !! index | member <- tuple, ChildIndex index <- group]
                    , ChildIndex position <- group
                    ]

{- | The number of keys above which 'countingRows' and 'intersectionCountingRows'
give up, and the number of transitions of one key above which
'intersectionCountingRows' gives up.
-}
countingLimit :: Int
countingLimit = 1024
