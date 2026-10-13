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

'sizedReference' builds each class that a query reads, and it keeps the
classes of each state for later queries. It is slow for large classes.
'sized' gives the same sequence. It counts, ranks, and unranks with the count
table of the cyclic import when the automaton has no constraint and that
import accepts it, and it uses the reference otherwise.
-}
module Data.CFTA.Sized (
    Sized,
    SizedError (..),
    sized,
    sizedReference,
    termsOfSize,
    countOfSize,
    unrankOfSize,
    rankOfSize,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IntMap
import Data.List (elemIndex, genericDrop, genericIndex, genericLength, sortOn)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalitiesHold, noConstraint, residual)
import Data.CFTA.Gen.Internal.Automaton (automatonIndex, automatonTermPosition, canonicalClasses)
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size (..))
import Data.CFTA.Interned (NodeId (..), fromFTA)
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Size (SizedRank (..), countAtSize, sizeClassSelect)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The size classes of an automaton, built on demand and kept.
data Sized symbol = Sized
    { sizedTerms :: Size -> [Term symbol]
    , sizedCount :: Size -> Cardinality
    , sizedUnrank :: Size -> ClassRank -> Maybe (Term symbol)
    , sizedRank :: Term symbol -> Maybe (Size, ClassRank)
    }

-- | Why 'sized' rejects an automaton.
data SizedError
    = -- | A transition has a guard beyond equality constraints.
      ResidualGuard
    deriving (Eq, Show)

{- | The size classes of an automaton.

The result is 'ResidualGuard' when a transition that the initial state can
reach has a guard beyond equality constraints.
-}
sized ::
    (Ord state, Ord symbol, Hashable symbol, Typeable symbol) =>
    FTA.FTA state symbol Constraint -> Either SizedError (Sized symbol)
sized automaton
    | all (all ((== noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable automaton)
    , Right index <- automatonIndex id root =
        let count = countAtSize index
            unrank size (ClassRank rank)
                | rank >= 0 && Cardinality rank < count size =
                    Just $ rankedValue $ sizeClassSelect index size (ClassRank rank)
                | otherwise = Nothing
            position = automatonTermPosition id root
         in Right
                Sized
                    { sizedTerms = \size -> [term | rank <- everyClassRank (count size), Just term <- [unrank size rank]]
                    , sizedCount = count
                    , sizedUnrank = unrank
                    , sizedRank = either (const Nothing) (\(SizedRank size rank) -> Just (size, rank)) . position
                    }
    | otherwise = sizedReference automaton
  where
    root = fromFTA automaton
    everyClassRank (Cardinality total) = map ClassRank [0 .. total - 1]

{- | The size classes of an automaton, each built from its definition.

The result is 'ResidualGuard' when a transition that the initial state can
reach has a guard beyond equality constraints.
-}
sizedReference :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Either SizedError (Sized symbol)
sizedReference automaton
    | any (any (residual . FTA.transitionConstraint)) (FTA.transitionTable $ FTA.trim automaton) = Left ResidualGuard
    | otherwise = Right $ fromClasses $ classAt $ FTA.initialState automaton
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

-- | The queries of the classes that a function lists.
fromClasses :: (Eq symbol) => (Size -> [Term symbol]) -> Sized symbol
fromClasses classOf =
    Sized
        { sizedTerms = classOf
        , sizedCount = Cardinality . genericLength . classOf
        , sizedUnrank = \size (ClassRank rank) ->
            if rank < 0 then Nothing else listToMaybe $ genericDrop rank $ classOf size
        , sizedRank = \term ->
            let size = Size $ toInteger $ length term
             in (,) size . ClassRank . toInteger <$> elemIndex term (classOf size)
        }

-- | The distinct accepted terms with the given number of nodes, in order.
termsOfSize :: Sized symbol -> Size -> [Term symbol]
termsOfSize = sizedTerms

-- | The number of distinct accepted terms with the given number of nodes.
countOfSize :: Sized symbol -> Size -> Cardinality
countOfSize = sizedCount

{- | The term at a class rank of a size class. 'Nothing' when the rank is
outside the class.
-}
unrankOfSize :: Sized symbol -> Size -> ClassRank -> Maybe (Term symbol)
unrankOfSize = sizedUnrank

{- | The size of a term and its class rank. 'Nothing' when the automaton does
not accept the term.
-}
rankOfSize :: Sized symbol -> Term symbol -> Maybe (Size, ClassRank)
rankOfSize = sizedRank
