{- | The inclusion of the language of one tree automaton in the language of
another, with a counterexample.

'inclusion' decides whether the right automaton accepts every term of the
left automaton. 'inclusionUpTo' decides it for the terms with at most the
given number of nodes. When the right automaton does not accept a term, both
give a smallest counterexample: a term that the left automaton accepts and
the right automaton rejects. Two automata are equivalent when each includes
the other.

'inclusionUpTo' compares counts. For each size from one to the bound, it counts
the terms of the left automaton and the terms of the intersection of the two
automata ('FTA.intersect'). The intersection accepts the common terms, so its
size class is a subset of the size class of the left automaton.
'countOfSize' counts each distinct term once, also when an automaton has
several runs for one term. Thus the two counts are equal exactly when the
right automaton accepts every term of the size class. At the first size where
the counts differ, the counterexample is the first term of the size class of
the left automaton that 'FTA.accepts' rejects for the right automaton. This is
the term with the smallest class rank. The order of a size class does not
depend on the names of the states. For an automaton without constraints, it
does not depend on the order of the rows either, so reordered copies of the
two automata give the same counterexample.

'inclusion' uses the bottom-up antichain algorithm of Bouajjani, Habermehl,
Holík, Touili, and Vojnar (/Antichain-Based Universality and Inclusion
Testing over Nondeterministic Finite Tree Automata/, CIAA 2008), which the
VATA library also implements (Lengál, Šimáček, and Vojnar, TACAS 2012). The
algorithm finds a counterexample, but not always a smallest one. Then
'inclusionUpTo', with the size of that counterexample as the bound, finds the
smallest one. Thus the two functions give the same counterexample.
'inclusionUpTo' stops at the first size where the counts differ, so this
step reads only the sizes up to the smallest counterexample.

An ambiguous automaton has several runs for some terms. 'sized' uses the
count table only when no state has two transitions that accept one term.
Otherwise it builds each size class term by term. An ambiguous automaton can
make the intersection ambiguous. Then the result is the same, but the time
grows with the number of terms.

'FTA.intersect' gives each transition the pair of the two constraints.
'conjoinConstraints' joins each pair into one 'Data.CFTA.Constraint.Constraint',
as 'sized' requires. A transition of the intersection then accepts a term
exactly when the two transitions accept it, so the intersection stays exact.
For two automata without constraints, the result is 'noConstraint' again, so
'sized' can use the count table.

The three checks decide different constraints. 'inclusion' accepts only
automata without constraints. 'inclusionUpTo' also accepts equality
constraints: 'sized' and 'FTA.accepts' check them on each term. A constraint
that a check does not decide gives 'ConstrainedLeft' or 'ConstrainedRight'.
The module does not remove a constraint, because 'FTA.dropConstraints' is an
over-approximation. Without the constraints of the left automaton, the
counterexample could be a term that the left automaton rejects. Without the
constraints of the right automaton, the check could miss a term that the
right automaton rejects.

'inclusionUpToWith' also decides guards beyond equality constraints, with a
solver ('sizedUpTo'). The solver can answer 'Unknown' for a guard on a term.
Then 'sizedUpTo' stops at the size of that term, and the check cannot decide
that size. The result is 'UnknownAt' with that size, unless a smaller size has
a counterexample. 'sizedUpTo' does not keep the classes below the size where
it stops, so the check builds them again with a smaller bound. The solver then
decides the guards below that size two times.

A partition check compares one automaton, the whole, with a list of automata,
the parts. The parts cover the whole when each term of the whole is a term of
some part. A term of the whole that no part accepts is a gap. The parts are
disjoint within the whole when no term of the whole is a term of two parts. A
term of the whole that two parts accept is an overlap. A term of two parts
that the whole rejects is not an overlap.

'partitionUpTo' intersects the whole with each part, and builds the union of
these intersections. For each size, the whole has a gap when the union has
fewer terms than the whole. It has an overlap when the sum of the counts of
the intersections is larger than the count of the union: the counts of finite
sets sum to the count of their union exactly when the sets are pairwise
disjoint. At the first such size, the check reads the size class of the
whole in order, and gives the first term that no part accepts, or the first
term that two parts accept. So a gap or an overlap is the smallest by size,
then by class rank in the whole, and an overlap names the two smallest part
indexes. 'partition' checks without a bound, for automata without
constraints. Its gap comes from 'inclusion' of the whole in the union. Its
overlap comes from the smallest term of the intersection of the whole with
two parts, for each pair of parts, and then from 'partitionUpTo' up to that
size.
-}
module Data.CFTA.Inclusion (
    Inclusion (..),
    InclusionError (..),
    inclusion,
    inclusionUpTo,
    inclusionUpToWith,

    -- * Partitions
    Partition (..),
    Cover (..),
    Disjointness (..),
    partition,
    partitionUpTo,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (conjoinConstraints, noConstraint, residual)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Index (Size (..))
import Data.CFTA.Refinement.Verdict (Entailment)
import Data.CFTA.Sized (Sized, SizedError (..), countOfSize, sized, sizedUpTo, termsOfSize)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)

-- | The result of an inclusion check.
data Inclusion symbol
    = -- | The right automaton accepts every term of the left automaton.
      Included
    | {- | The right automaton accepts every term of the left automaton with at
      most this number of nodes. Larger terms are not checked.
      -}
      IncludedUpTo !Size
    | {- | A counterexample: a term that the left automaton accepts and the
      right automaton rejects. No counterexample has fewer nodes, and no
      counterexample of the same size has a smaller class rank in the left
      automaton.
      -}
      NotIncluded !(Term symbol)
    | {- | The right automaton accepts every term of the left automaton with
      fewer nodes than this size. The solver did not decide a constraint on a
      term with this number of nodes, which the left automaton or the
      intersection builds at one of its states. So this size and the larger
      sizes are not checked. A counterexample of this size is not given,
      because the check cannot find the one with the smallest class rank.
      -}
      UnknownAt !Size
    deriving (Eq, Show)

{- | Why an inclusion check cannot start. For a partition check, the whole is
the left automaton, and each part is a right automaton.
-}
data InclusionError
    = -- | A transition of the left automaton has a constraint that the check does not decide.
      ConstrainedLeft
    | -- | A transition of the right automaton has a constraint that the check does not decide.
      ConstrainedRight
    deriving (Eq, Show)

-- | The result of a partition check.
data Partition symbol = Partition
    { partitionCover :: !(Cover symbol)
    -- ^ Whether the parts cover the whole.
    , partitionDisjointness :: !(Disjointness symbol)
    -- ^ Whether the parts are disjoint within the whole.
    }
    deriving (Eq, Show)

-- | Whether each term of the whole is a term of some part.
data Cover symbol
    = -- | Each term of the whole is a term of some part.
      Covered
    | {- | Each term of the whole with at most this number of nodes is a term of
      some part. Larger terms are not checked.
      -}
      CoveredUpTo !Size
    | {- | A gap: a term of the whole that no part accepts. No gap has fewer
      nodes, and no gap of the same size has a smaller class rank in the
      whole.
      -}
      Gap !(Term symbol)
    deriving (Eq, Show)

-- | Whether no term of the whole is a term of two parts.
data Disjointness symbol
    = -- | No term of the whole is a term of two parts.
      Disjoint
    | {- | No term of the whole with at most this number of nodes is a term of
      two parts. Larger terms are not checked.
      -}
      DisjointUpTo !Size
    | {- | An overlap: a term of the whole that two parts accept, and the indexes
      of the first two parts that accept it, in ascending order. No overlap
      has fewer nodes, and no overlap of the same size has a smaller class
      rank in the whole.
      -}
      Overlap !(Term symbol) !Int !Int
    deriving (Eq, Show)

{- | Whether the right automaton accepts every term of the left automaton, or
a smallest counterexample. The result is 'Included' or 'NotIncluded'.

The two automata must have no constraints. The check reads every row of the
two automata for constraints, also a row that the initial state cannot reach.
-}
inclusion ::
    (Ord left, Ord right, Ord symbol) =>
    FTA.PlainFTA left symbol -> FTA.PlainFTA right symbol -> Either InclusionError (Inclusion symbol)
inclusion left right
    | constrained left = Left ConstrainedLeft
    | constrained right = Left ConstrainedRight
    | otherwise = case counterexampleSize left right of
        Nothing -> Right Included
        Just size -> case inclusionUpTo size left right of
            smallest@(Right (NotIncluded _)) -> smallest
            _ -> bug "the bounded check finds no counterexample up to the size of one"

{- | Whether the right automaton accepts every term of the left automaton with
at most the given number of nodes, or a smallest counterexample. The result
is 'IncludedUpTo' or 'NotIncluded'.

The two automata can have equality constraints, but no guard beyond them. The
check reads every row of the two automata for such a guard, also a row that
the initial state cannot reach. A bound below one gives 'IncludedUpTo' with
that bound, because each term has at least one node.
-}
inclusionUpTo ::
    (Ord left, Ord right, Ord symbol) =>
    Size -> FTA.PlainFTA left symbol -> FTA.PlainFTA right symbol -> Either InclusionError (Inclusion symbol)
inclusionUpTo bound left right
    | guarded left = Left ConstrainedLeft
    | guarded right = Left ConstrainedRight
    | otherwise =
        Right $ firstMissing bound (classes left) (classes $ intersection left right) (const $ not . FTA.accepts right)

{- | 'inclusionUpTo' for automata with any constraints. The solver decides each
constraint on each term that its transition builds. The result is
'IncludedUpTo', 'NotIncluded', or 'UnknownAt'.

When the solver does not decide a constraint on a term of the left automaton
or of the intersection, the check stops at the size of that term. It then
checks the sizes below it again. A counterexample there gives 'NotIncluded';
otherwise the result is 'UnknownAt' with the size where the check stopped.
The check calls the solver for each term up to the bound, also when a
smaller size has a counterexample.
-}
inclusionUpToWith ::
    (Ord left, Ord right) =>
    Entailment -> Size -> FTA.PlainFTA left Symbol -> FTA.PlainFTA right Symbol -> IO (Inclusion Symbol)
inclusionUpToWith entailment bound left right = do
    leftClasses <- sizedUpTo entailment bound left
    case leftClasses of
        Left stop -> below stop
        Right decidedLeft -> do
            commonClasses <- sizedUpTo entailment bound (intersection left right)
            case commonClasses of
                Left stop -> below stop
                Right decidedCommon -> pure $ firstMissing bound decidedLeft decidedCommon (missingFrom decidedCommon)
  where
    -- A term of the left class that the class of the intersection does not hold.
    missingFrom decidedCommon size = (`Set.notMember` Set.fromList (termsOfSize decidedCommon size))
    -- The result below the size of a term that the solver did not decide.
    below (GuardUnknown _ term) = do
        let stop = Size $ toInteger $ length term
        smaller <- inclusionUpToWith entailment (stop - 1) left right
        pure $ case smaller of
            IncludedUpTo _ -> UnknownAt stop
            decided -> decided
    below ResidualGuard = bug "sizedUpTo rejects a guard"

{- | The size of a counterexample, or 'Nothing' when the right automaton
accepts every term of the left automaton. The automata have no constraints.

This is the bottom-up antichain algorithm. A pair holds a state of the left
automaton and the set of the states of the right automaton that accept one
term of that left state, with the size of that term. The pairs grow from the
leaves up: a transition of the left automaton joins one pair for each child
into a pair for its parent. The set of the new pair holds each right parent
of a right transition with the same symbol whose children are in the sets of
the joined pairs. A pair of the initial left state is a counterexample when
its set does not hold the initial right state.

A pair with a smaller set subsumes a pair of the same left state with a
larger set: each join with the larger set gives a larger set than the same
join with the smaller set. So the search keeps only the pairs with minimal
sets for each left state, an antichain. Each new pair joins with the pairs
that the search keeps. The search stops at a counterexample, or when no new
pair remains. The number of sets is finite, so the search ends.
-}
counterexampleSize ::
    (Ord left, Ord right, Ord symbol) => FTA.PlainFTA left symbol -> FTA.PlainFTA right symbol -> Maybe Size
counterexampleSize left right =
    search Map.empty [(parent, accepting symbol [], 1) | (parent, FTA.Transition symbol [] _) <- leftTransitions]
  where
    leftTransitions = [(parent, transition) | (parent, transitions) <- Map.toList (FTA.transitionTable left), transition <- transitions]
    -- The transitions of the left automaton with each child state.
    users =
        Map.fromListWith
            (flip (<>))
            [ (child, [(parent, transition)])
            | (parent, transition) <- leftTransitions
            , child <- nubOrd (FTA.transitionChildren transition)
            ]
    -- The children and parent of each transition of the right automaton, by symbol and arity.
    rightTransitions =
        Map.fromListWith
            (flip (<>))
            [ ((FTA.transitionSymbol transition, length children), [(children, parent)])
            | (parent, transitions) <- Map.toList (FTA.transitionTable right)
            , transition <- transitions
            , let children = FTA.transitionChildren transition
            ]
    -- The right states that accept a term with this symbol and with children in these sets.
    accepting symbol sets =
        Set.fromList
            [ parent
            | (children, parent) <- Map.findWithDefault [] (symbol, length sets) rightTransitions
            , and (zipWith Set.member children sets)
            ]

    search _ [] = Nothing
    search kept ((state, set, size) : pending)
        | any ((`Set.isSubsetOf` set) . fst) known = search kept pending
        | state == FTA.initialState left && Set.notMember (FTA.initialState right) set = Just size
        | otherwise = search kept' (joined <> pending)
      where
        known = Map.findWithDefault [] state kept
        kept' = Map.insert state ((set, size) : filter (not . (set `Set.isSubsetOf`) . fst) known) kept
        -- The joins with the new pair at one child and kept pairs at the other children.
        joined =
            [ (parent, accepting (FTA.transitionSymbol transition) (map fst choice), 1 + sum (map snd choice))
            | (parent, transition) <- Map.findWithDefault [] state users
            , let children = zip [0 :: Int ..] (FTA.transitionChildren transition)
            , position <- [index | (index, child) <- children, child == state]
            , choice <-
                traverse (\(index, child) -> if index == position then [(set, size)] else Map.findWithDefault [] child kept') children
            ]

{- | The first size up to the bound where the class of the intersection is
smaller than the class of the left automaton, with the first term of the left
class that is missing from the right automaton at that size.
-}
firstMissing :: Size -> Sized symbol -> Sized symbol -> (Size -> Term symbol -> Bool) -> Inclusion symbol
firstMissing bound leftClasses commonClasses missing = case filter differs [1 .. bound] of
    [] -> IncludedUpTo bound
    size : _ ->
        NotIncluded
            $ fromMaybe (bug "a size class of the intersection is smaller, but no term is missing")
            $ find (missing size) (termsOfSize leftClasses size)
  where
    differs size = countOfSize leftClasses size /= countOfSize commonClasses size

-- | The intersection of two automata, with the conjunction of the two constraints on each transition.
intersection ::
    (Ord left, Ord right, Ord symbol) =>
    FTA.PlainFTA left symbol -> FTA.PlainFTA right symbol -> FTA.PlainFTA (FTA.ProductState left right) symbol
intersection left right =
    FTA.mapConstraints (uncurry conjoinConstraints) $ FTA.intersect left right

{- | Whether the parts cover the whole and are disjoint within it, for the terms
with at most the given number of nodes. The cover is 'CoveredUpTo' or 'Gap',
and the disjointness is 'DisjointUpTo' or 'Overlap'.

The automata can have equality constraints, but no guard beyond them, as for
'inclusionUpTo'. A guard in the whole gives 'ConstrainedLeft', and a guard in
a part gives 'ConstrainedRight'. An overlap makes the union ambiguous, so
'sized' builds the classes of the union term by term.
-}
partitionUpTo ::
    (Ord whole, Ord part, Ord symbol) =>
    Size -> FTA.PlainFTA whole symbol -> [FTA.PlainFTA part symbol] -> Either InclusionError (Partition symbol)
partitionUpTo bound whole parts
    | guarded whole = Left ConstrainedLeft
    | any guarded parts = Left ConstrainedRight
    | otherwise = Right $ Partition cover disjointness
  where
    wholeClasses = classes whole
    products = map (intersection whole) parts
    productClasses = map classes products
    unionClasses = classes $ union products
    firstSize differs = find differs [1 .. bound]
    cover = case firstSize (\size -> countOfSize wholeClasses size /= countOfSize unionClasses size) of
        Nothing -> CoveredUpTo bound
        Just size ->
            Gap
                $ fromMaybe (bug "the union is smaller than the whole, but no term is missing")
                $ find (null . accepting) (termsOfSize wholeClasses size)
    disjointness = case firstSize (\size -> sum (map (`countOfSize` size) productClasses) /= countOfSize unionClasses size) of
        Nothing -> DisjointUpTo bound
        Just size ->
            fromMaybe (bug "the intersections are larger than their union, but no term is in two parts") $
                listToMaybe [Overlap term first second | term <- termsOfSize wholeClasses size, first : second : _ <- [accepting term]]
    -- The indexes of the parts that accept a term.
    accepting term = [index | (index, part) <- zip [0 ..] parts, FTA.accepts part term]

{- | Whether the parts cover the whole and are disjoint within it. The cover is
'Covered' or 'Gap', and the disjointness is 'Disjoint' or 'Overlap'. They are
the gap and the overlap that 'partitionUpTo' gives.

The automata must have no constraints, as for 'inclusion'. The cover is the
inclusion of the whole in the union of its intersections with the parts. The
disjointness reads the intersection of the whole with each pair of parts: it
is empty, or it has a smallest term. So the check builds a number of products
that grows with the square of the number of parts.
-}
partition ::
    (Ord whole, Ord part, Ord symbol) =>
    FTA.PlainFTA whole symbol -> [FTA.PlainFTA part symbol] -> Either InclusionError (Partition symbol)
partition whole parts
    | constrained whole = Left ConstrainedLeft
    | any constrained parts = Left ConstrainedRight
    | otherwise = Right $ Partition cover disjointness
  where
    products = map (intersection whole) parts
    cover = case inclusion whole (union products) of
        Right Included -> Covered
        Right (NotIncluded gap) -> Gap gap
        _ -> bug "the inclusion of two automata without constraints is not decided"
    -- The smallest overlap of each pair of parts, by the intersection of the
    -- whole and the first part with the second part.
    overlapSizes =
        [ size
        | (index, withPart) <- zip [0 ..] products
        , other <- drop (index + 1) parts
        , Just size <- [smallestSize $ intersection withPart other]
        ]
    disjointness = case overlapSizes of
        [] -> Disjoint
        sizes -> case partitionUpTo (minimum sizes) whole parts of
            Right (Partition _ found@Overlap{}) -> found
            _ -> bug "the bounded check finds no overlap up to the size of one"
    smallestSize automaton = Map.lookup (FTA.initialState automaton) $ Ordinary.minimumSizes $ FTA.transitionTable automaton

{- | The union of automata. A new initial state has the transitions of the
initial states of all of them. The automata must give each symbol one arity.
-}
union :: (Ord state) => [FTA.PlainFTA state symbol] -> FTA.PlainFTA (Maybe (Int, state)) symbol
union automata =
    fromRight (bug "the union of the intersections with one whole is not ranked")
        $ FTA.mkFTA Nothing
        $ ( Nothing
          , concat [map (tagged index) $ FTA.transitionsFrom automaton $ FTA.initialState automaton | (index, automaton) <- indexed]
          )
            : [ (Just (index, state), map (tagged index) transitions)
              | (index, automaton) <- indexed
              , (state, transitions) <- Map.toList $ FTA.transitionTable automaton
              ]
  where
    indexed = zip [0 ..] automata
    tagged index transition = transition{FTA.transitionChildren = map (Just . (index,)) $ FTA.transitionChildren transition}

-- | The size classes of an automaton without a guard beyond equality constraints.
classes :: (Ord state, Ord symbol) => FTA.PlainFTA state symbol -> Sized symbol
classes automaton = fromRight (bug "an automaton without a residual guard has one") $ sized automaton

-- | Whether a transition of an automaton has a guard beyond equality constraints.
guarded :: FTA.PlainFTA state symbol -> Bool
guarded = any (any (residual . FTA.transitionConstraint)) . FTA.transitionTable

-- | Whether a transition of an automaton has a constraint.
constrained :: FTA.PlainFTA state symbol -> Bool
constrained = any (any ((/= noConstraint) . FTA.transitionConstraint)) . FTA.transitionTable

-- | Stop with an error that names this module.
bug :: String -> a
bug message = error $ "cfta-generator bug in Data.CFTA.Inclusion: " <> message
