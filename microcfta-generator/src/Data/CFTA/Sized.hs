{- | The terms of one size that a finite tree automaton accepts: listed,
counted, ranked, and unranked as one sequence.

The size of a term is its number of nodes. A size class holds the distinct
terms of one size that the automaton accepts, each once. 'termsOfSize',
'countOfSize', 'unrankOfSize', and 'rankOfSize' describe the same class in the
same order, so 'unrankOfSize' and 'rankOfSize' are inverse on it.

Every query for a size ends. The class of size @n@ is built from the classes
of the child states at smaller sizes, because each child of a term has fewer
nodes than the term. So a cycle in the automaton cannot make a query loop,
and an empty class says nothing about the classes after it.

The order is the order of the count table of the cyclic import
('Data.CFTA.Gen.fromAutomaton'):

* The transitions of a state are sorted by their arity, their symbol, and the
  canonical classes of their child states, so the order does not depend on
  the order in which the automaton lists them. States that the initial state
  cannot reach do not change the order.
* A transition @f(c1, ..., ck)@ lists the nested product
  @((f × c1) × c2) ... × ck@. Each product goes through the sizes of its
  left side in ascending order, and through the terms of each split
  left-major.
* A term that several transitions accept keeps its first place.

Where that import accepts the automaton (no constraint and no ambiguity), it
gives each term the same size and class rank as this module.

Equality constraints are checked on each term that their transition builds,
so the classes are exact. A guard beyond equality constraints has no decision
procedure here, and 'sized' rejects it.

This is the reference: it builds each class that a query reads, and it keeps
the classes of each state for later queries. It is slow for large classes.
-}
module Data.CFTA.Sized (
    Sized,
    SizedError (..),
    sized,
    termsOfSize,
    countOfSize,
    unrankOfSize,
    rankOfSize,
) where

import Data.Containers.ListUtils (nubOrd)
import qualified Data.IntMap.Strict as IntMap
import Data.List (elemIndex, genericDrop, genericIndex, genericLength, sortOn)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalitiesHold, residual)
import Data.CFTA.Gen.Internal.Automaton (canonicalClasses)
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size (..))
import Data.CFTA.Interned (NodeId (..))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The size classes of an automaton, built on demand and kept.
newtype Sized symbol = Sized (Size -> [Term symbol])

-- | Why 'sized' rejects an automaton.
data SizedError
    = -- | A transition has a guard beyond equality constraints.
      ResidualGuard
    deriving (Eq, Show)

{- | The size classes of an automaton.

The result is 'ResidualGuard' when a transition that the initial state can
reach has a guard beyond equality constraints.
-}
sized :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Either SizedError (Sized symbol)
sized automaton
    | any (any (residual . FTA.transitionConstraint)) (FTA.transitionTable $ FTA.trim automaton) = Left ResidualGuard
    | otherwise = Right $ Sized $ classAt $ FTA.initialState automaton
  where
    -- The classes are those of the whole graph, as in the import. A trim
    -- would remove the transitions with a child that accepts nothing, and
    -- that can change the order of the classes of the other states.
    rows = Map.map (sortOn rowKey) (FTA.transitionTable automaton)

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

    -- The classes of each state from size one, built when a query reads them.
    table = LazyMap.map (\transitions -> [classOf transitions size | size <- [1 ..]]) rows
    classAt state (Size size)
        | size < 1 = []
        | otherwise = maybe [] (`genericIndex` (size - 1)) (LazyMap.lookup state table)

    classOf transitions size = nubOrd $ concatMap (transitionTerms size) transitions
    transitionTerms size transition =
        filter
            (equalitiesHold $ FTA.transitionConstraint transition)
            [ Term.Node (FTA.transitionSymbol transition) arguments
            | arguments <- argumentsOf (FTA.transitionChildren transition) (size - 1)
            ]

    -- The argument lists of the children with the given total size, in the
    -- order of the nested product: the last child varies fastest, and each
    -- product goes through the sizes of its left side in ascending order.
    argumentsOf children total = map reverse $ go (reverse children) total
      where
        go [] remaining = [[] | remaining == 0]
        go (current : before) remaining =
            [ term : arguments
            | left <- [0 .. remaining]
            , arguments <- go before left
            , term <- classAt current (remaining - left)
            ]

-- | The distinct accepted terms with the given number of nodes, in order.
termsOfSize :: Sized symbol -> Size -> [Term symbol]
termsOfSize (Sized classOf) = classOf

-- | The number of distinct accepted terms with the given number of nodes.
countOfSize :: Sized symbol -> Size -> Cardinality
countOfSize classes = Cardinality . genericLength . termsOfSize classes

{- | The term at a class rank of a size class. 'Nothing' when the rank is
outside the class.
-}
unrankOfSize :: Sized symbol -> Size -> ClassRank -> Maybe (Term symbol)
unrankOfSize classes size (ClassRank rank)
    | rank < 0 = Nothing
    | otherwise = listToMaybe $ genericDrop rank $ termsOfSize classes size

{- | The size of a term and its class rank. 'Nothing' when the automaton does
not accept the term.
-}
rankOfSize :: (Eq symbol) => Sized symbol -> Term symbol -> Maybe (Size, ClassRank)
rankOfSize classes term = (,) size . ClassRank . toInteger <$> elemIndex term (termsOfSize classes size)
  where
    size = Size $ toInteger $ length term
