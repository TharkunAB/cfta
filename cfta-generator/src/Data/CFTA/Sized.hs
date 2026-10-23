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

The order uses the original graph rows and the nested products of the count
table shared with the cyclic import ('Data.CFTA.Gen.fromAutomaton'):

* The transitions of a state are sorted by their arity, their symbol, and the
  canonical classes of their child states, so the order does not depend on
  the order in which the automaton lists them. States that the initial state
  cannot reach do not change the order.
* A transition @f(c1, ..., ck)@ lists the nested product
  @((f × c1) × c2) ... × ck@. Each product goes through the sizes of its
  left side in ascending order, and through the terms of each split
  left-major.
* A term that several transitions accept keeps its first place.

The count table reads these original rows. Importing through interned nodes
can trim dead edges or remove duplicate edges. Those changes can change
canonical row order even when they preserve the language.

Equality constraints are checked on each term that their transition builds,
so the classes are exact. A guard beyond equality constraints has no decision
procedure here, and 'sized' rejects it.

'sizedReference' builds each class that a query reads, and it keeps the
classes of each state for later queries. It is slow for large classes.
'sizedUpTo' builds the classes up to a size bound with a solver that decides
every guard, so it needs no pruning: it is the exact route for a liquid
automaton whose guards pruning did not discharge.
'sized' gives the same sequence. It counts, ranks, and unranks with the count
table when the automaton has no constraint and its rows are unambiguous.
It uses the reference otherwise. 'sizedStates' gives the classes of each
state, with one table for all the states.
-}
module Data.CFTA.Sized (
    Sized,
    SizedError (..),
    sized,
    sizedReference,
    sizedStates,
    sizedUpTo,
    termsOfSize,
    countOfSize,
    unrankOfSize,
    rankOfSize,
) where

import Control.Monad (filterM, foldM, void)
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Containers.ListUtils (nubOrd)
import qualified Data.IntMap.Strict as IntMap
import Data.List (elemIndex, genericDrop, genericIndex, genericLength, sortOn)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalitiesHold, noConstraint, residual)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size (..))
import Data.CFTA.Interned (NodeId (..), canonicalClasses)
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Size (SizedRank (..), countAtSize, sizeClassSelect)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The size classes of an automaton, built on demand and kept.
data Sized symbol = Sized
    { sizedTerms :: Size -> [Term symbol]
    , sizedCount :: Size -> Cardinality
    , sizedUnrank :: Size -> ClassRank -> Maybe (Term symbol)
    , sizedRank :: Term symbol -> Maybe (Size, ClassRank)
    }

-- | Why a size class cannot be built.
data SizedError
    = -- | A transition has a guard beyond equality constraints.
      ResidualGuard
    | -- | The solver could not decide a constraint on a term that its transition built.
      GuardUnknown !Constraint !(Term Symbol)
    deriving (Eq, Show)

{- | The size classes of an automaton.

The result is 'ResidualGuard' when a transition that the initial state can
reach has a guard beyond equality constraints.
-}
sized ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol Constraint -> Either SizedError (Sized symbol)
sized automaton = ($ FTA.initialState automaton) <$> sizedStates automaton

{- | The size classes of each state of an automaton, with one count table for
all the states. For each state that the initial state reaches, the classes
are those that 'sized' gives with that state as the initial state.

The result is 'ResidualGuard' when a transition that the initial state can
reach has a guard beyond equality constraints. A guard on a transition that
the initial state cannot reach is not checked, so the classes of a state that
the initial state does not reach can hold too many terms. Do not read them.
A rank query of a state builds a position table for that state.
-}
sizedStates ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol Constraint -> Either SizedError (state -> Sized symbol)
sizedStates automaton
    | all (all ((== noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable automaton)
    , Ordinary.unambiguousRows rows =
        Right $ \state ->
            let index = indexOf state
                count = countAtSize index
                unrank size (ClassRank rank)
                    | rank >= 0 && Cardinality rank < count size =
                        Just $ rankedValue $ sizeClassSelect index size (ClassRank rank)
                    | otherwise = Nothing
                position = Ordinary.tablePosition state rows
             in Sized
                    { sizedTerms = \size -> [term | rank <- everyClassRank (count size), Just term <- [unrank size rank]]
                    , sizedCount = count
                    , sizedUnrank = unrank
                    , sizedRank = fmap (\(SizedRank size rank) -> (size, rank)) . position
                    }
    | otherwise = referenceStates automaton
  where
    rows = Map.map (map void) $ sortedRows automaton
    indexOf = Ordinary.tableIndexes rows
    everyClassRank (Cardinality total) = map ClassRank [0 .. total - 1]

{- | The size classes of an automaton, each built from its definition.

The result is 'ResidualGuard' when a transition that the initial state can
reach has a guard beyond equality constraints.
-}
sizedReference :: (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Either SizedError (Sized symbol)
sizedReference automaton = ($ FTA.initialState automaton) <$> referenceStates automaton

{- | The size classes of each state of an automaton, each built from its
definition, as 'sizedReference' builds them for the initial state.
-}
referenceStates ::
    (Ord state, Ord symbol) => FTA.FTA state symbol Constraint -> Either SizedError (state -> Sized symbol)
referenceStates automaton
    | any (any (residual . FTA.transitionConstraint)) (FTA.transitionTable $ FTA.trim automaton) = Left ResidualGuard
    | otherwise = Right $ fromClasses . classAt
  where
    rows = sortedRows automaton

    -- The classes of each state from size one, built when a query reads them.
    table = LazyMap.map (\transitions -> [classOf transitions size | size <- [1 ..]]) rows
    classAt state (Size size)
        | size < 1 = []
        | otherwise = maybe [] (`genericIndex` (size - 1)) (LazyMap.lookup state table)
    classOf transitions size =
        nubOrd
            [ term
            | transition <- transitions
            , term <- candidates classAt transition size
            , equalitiesHold (FTA.transitionConstraint transition) term
            ]

{- | The size classes of the terms with at most the given number of nodes, with
the solver deciding every constraint on each term that its transition builds.

The classes are those of 'sizedReference' for the language of the terms up to
the bound, and a class above the bound is empty. A guard beyond equality
constraints is decided too, so no guard is rejected. The result is
'GuardUnknown' when the solver cannot decide a constraint on a term. Only the
states that the initial state can reach are decided.
-}
sizedUpTo ::
    (Ord state) => Entailment -> Size -> FTA.FTA state Symbol Constraint -> IO (Either SizedError (Sized Symbol))
sizedUpTo entailment bound automaton = runExceptT $ do
    table <- foldM addSize Map.empty [1 .. bound]
    pure $ fromClasses $ \size -> Map.findWithDefault [] (FTA.initialState automaton, size) table
  where
    rows = sortedRows automaton
    reached = Map.keys $ FTA.transitionTable $ FTA.trim automaton
    -- The classes of one size, from the classes of the smaller sizes.
    addSize table size = foldM addClass table reached
      where
        smaller state child = Map.findWithDefault [] (state, child) table
        addClass built state = do
            accepted <-
                filterM
                    decide
                    [ (transition, term)
                    | transition <- Map.findWithDefault [] state rows
                    , term <- candidates smaller transition size
                    ]
            pure $ Map.insert (state, size) (nubOrd $ map snd accepted) built
    decide (transition, term) = do
        let constraint = FTA.transitionConstraint transition
        verdict <- liftIO $ evaluateConstraint entailment constraint term
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> throwError $ GuardUnknown constraint term

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

{- | The terms of the given size that a transition builds from the classes of
its children, before its constraint is checked, in the order of the nested
product: the last child varies fastest, and each product goes through the
sizes of its left side in ascending order.
-}
candidates :: (state -> Size -> [Term symbol]) -> FTA.Transition state symbol constraint -> Size -> [Term symbol]
candidates classAt transition size =
    [ Term.Node (FTA.transitionSymbol transition) (reverse arguments)
    | arguments <- go (reverse $ FTA.transitionChildren transition) (size - 1)
    ]
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
