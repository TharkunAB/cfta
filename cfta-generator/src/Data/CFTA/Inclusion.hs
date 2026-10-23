{- | The inclusion of the language of one tree automaton in the language of
another, up to a size bound, with a counterexample.

'inclusionUpTo' decides whether the right automaton accepts every term of the
left automaton with at most the given number of nodes. When it does not, the
result is a smallest counterexample: a term that the left automaton accepts
and the right automaton rejects. Two automata are equivalent up to a bound
when each includes the other up to that bound.

The decision compares counts. For each size from one to the bound, it counts
the terms of the left automaton and the terms of the intersection of the two
automata ('FTA.intersect'). The intersection accepts the common terms, so its
size class is a subset of the size class of the left automaton.
'countOfSize' counts each distinct term once, also when an automaton has
several runs for one term. Thus the two counts are equal exactly when the
right automaton accepts every term of the size class. At the first size where
the counts differ, the counterexample is the first term of the size class of
the left automaton that 'FTA.accepts' rejects for the right automaton. This is
the term with the smallest class rank. The order of a size class does not
depend on the order of the rows or on the names of the states, so reordered
copies of the two automata give the same counterexample.

An ambiguous automaton has several runs for some terms. 'sized' uses the
count table only when no state has two transitions that accept one term.
Otherwise it builds each size class term by term. An ambiguous automaton can
make the intersection ambiguous. Then the result is the same, but the time
grows with the number of terms.

This version accepts only automata without constraints: each transition must
have 'noConstraint'. A constraint gives 'ConstrainedLeft' or
'ConstrainedRight'. The module does not remove a constraint, because
'FTA.dropConstraints' is an over-approximation. Without the constraints of
the left automaton, the counterexample could be a term that the left
automaton rejects. Without the constraints of the right automaton, the check
could miss a term that the right automaton rejects.

'FTA.intersect' gives each transition the pair of the two constraints.
'conjoinConstraints' joins each pair into one 'Data.CFTA.Constraint.Constraint',
as 'sized' requires. For two automata without constraints, the result is
'noConstraint' again, so 'sized' can use the count table.
-}
module Data.CFTA.Inclusion (
    Inclusion (..),
    InclusionError (..),
    inclusionUpTo,
) where

import Data.Either (fromRight)
import Data.List (find)
import Data.Maybe (fromMaybe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (conjoinConstraints, noConstraint)
import Data.CFTA.Index (Size)
import Data.CFTA.Sized (countOfSize, sized, termsOfSize)
import Data.CFTA.Term (Term)

-- | The result of an inclusion check up to a size bound.
data Inclusion symbol
    = {- | The right automaton accepts every term of the left automaton with at
      most this number of nodes. Larger terms are not checked.
      -}
      IncludedUpTo !Size
    | {- | A counterexample: a term that the left automaton accepts and the
      right automaton rejects. No counterexample has fewer nodes, and no
      counterexample of the same size has a smaller class rank in the left
      automaton.
      -}
      NotIncluded !(Term symbol)
    deriving (Eq, Show)

-- | Why an inclusion check cannot start.
data InclusionError
    = -- | A transition of the left automaton has a constraint.
      ConstrainedLeft
    | -- | A transition of the right automaton has a constraint.
      ConstrainedRight
    deriving (Eq, Show)

{- | Whether the right automaton accepts every term of the left automaton with
at most the given number of nodes, or a smallest counterexample.

The check reads every row of the two automata for constraints, also a row
that the initial state cannot reach. A bound below one gives 'IncludedUpTo'
with that bound, because each term has at least one node.
-}
inclusionUpTo ::
    (Ord left, Ord right, Ord symbol) =>
    Size -> FTA.PlainFTA left symbol -> FTA.PlainFTA right symbol -> Either InclusionError (Inclusion symbol)
inclusionUpTo bound left right
    | constrained left = Left ConstrainedLeft
    | constrained right = Left ConstrainedRight
    | otherwise = Right $ case filter differs [1 .. bound] of
        [] -> IncludedUpTo bound
        size : _ ->
            NotIncluded
                $ fromMaybe (bug "a size class of the intersection is smaller, but no term is missing")
                $ find (not . FTA.accepts right) (termsOfSize leftClasses size)
  where
    constrained = any (any ((/= noConstraint) . FTA.transitionConstraint)) . FTA.transitionTable
    differs size = countOfSize leftClasses size /= countOfSize commonClasses size
    leftClasses = classes left
    commonClasses =
        classes
            $ FTA.mapConstraints (uncurry conjoinConstraints)
            $ fromRight (bug "the intersection of two ranked automata is not ranked")
            $ FTA.intersect left right
    classes automaton = fromRight (bug "an automaton without constraints has a guard") $ sized automaton
    bug message = error $ "cfta-generator bug in Data.CFTA.Inclusion: " <> message
