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

The order of 'sizedReference' uses the original graph rows and the nested
products of the count table shared with the cyclic import
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

The routes @sized@ and @sized-sample@ of "Data.CFTA.Sized.Checkpoint" use
the order of 'sized'. A change to the order must increase the versions of both
routes, so that an old checkpoint does not resume in the new order.

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
'sized' gives the classes of the reference. It counts, ranks, and unranks
with a count table, without a list of the terms, when the rows that the
initial state reaches are of one of these kinds:

* Rows without constraints that are unambiguous. The table reads the rows,
  and the order is the order of the reference. Bottom-up deterministic rows,
  as in an e-graph, are unambiguous. A set of transition keys checks this
  condition first.
* Rows without constraints that are ambiguous. The table reads the bottom-up
  deterministic rows of all the rows of the automaton. A deterministic state
  is the set of the states that accept one term, so each term has one run.
  The row of a state holds the transitions of each deterministic state that
  contains the state. The order is the order of the reference for these rows.
* Rows that are unambiguous without their constraints, where each constraint
  is equalities between direct children. The table reads the rows of the
  intersections of the states. A class of equal children is one child: the
  intersection of its child states. Its term fills each position of the
  class, and its size counts once for each position. The order is the order
  of the reference for the rows of the intersections, with the classes of
  equal children as a part of the symbol. A transition lists the nested
  product of its groups of children, in the order of their first positions.

The second and the third kind stop at 1024 deterministic states or
intersections, and 'sized' then uses the reference. 'sized' also uses the
reference for all other rows, for example an equality below the direct
children, or ambiguous rows with constraints. For the second and the third
kind, the order can be different from the order of the reference.
'sizedStates' gives the classes of each state. The states without constraints
share one table, and each state with equal children has its own table.
-}
module Data.CFTA.Sized (
    Sized,
    SizedError (..),
    sized,
    sizedReference,
    sizedStates,
    sizedUpTo,
    termsOfSize,
    termsOfSizeFrom,
    countOfSize,
    unrankOfSize,
    rankOfSize,
) where

import Control.Monad (filterM, foldM, void)
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.List (elemIndex, genericDrop, genericIndex, genericLength)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalitiesHold, noConstraint, residual)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size (..))
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Size (SizedRank (..), countAtSize, sizeClassSelect)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | The size classes of an automaton, built on demand and kept.
data Sized symbol = Sized
    { sizedTermsFrom :: Size -> ClassRank -> [Term symbol]
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

{- | The size classes of each state of an automaton. The states without
constraints share one count table, and each state with equal children has its
own table. For each state that the initial state reaches, the classes are
those that 'sized' gives with that state as the initial state. A state
that the initial state does not reach, or that accepts no term, has no terms
here: its guards are not checked.

The result is 'ResidualGuard' when a transition that the initial state can
reach has a guard beyond equality constraints. A rank query of a state builds
a position table for that state.
-}
sizedStates ::
    (Ord state, Ord symbol) =>
    FTA.FTA state symbol Constraint -> Either SizedError (state -> Sized symbol)
sizedStates automaton = route <$> referenceStates automaton
  where
    reached = FTA.transitionTable $ FTA.trim automaton
    route reference state = case LazyMap.lookup state tables of
        Nothing -> fromClasses (const [])
        Just table -> fromMaybe (reference state) table
    -- The route of each state follows the rows that it reaches, as 'sized' of
    -- the automaton with that initial state does, so the two agree.
    tables = LazyMap.fromList [(state, tableClasses state) | state <- Map.keys reached]
    tableClasses state
        | all (all ((== noConstraint) . FTA.transitionConstraint)) rows =
            if unambiguous then Just (plain state) else ($ state) <$> deterministic
        | unambiguous = (\table -> fromTable table Set.singleton state) <$> Ordinary.intersectionCountingRows rows state
        | otherwise = Nothing
      where
        rows = FTA.transitionTable $ FTA.trim $ withInitial state
        unambiguous = Ordinary.unambiguousRows (Map.map (map void) rows)
    withInitial state =
        fromRight (error "sizedStates: a state of a valid automaton is a valid initial state") $
            FTA.mkFTA state (Map.toList $ FTA.transitionTable automaton)
    unconstrained = FTA.mapConstraints (const ()) automaton
    plain = fromTable (withoutClasses $ Ordinary.plainCountingRows unconstrained) Left
    deterministic = (`fromTable` Left) . withoutClasses <$> Ordinary.deterministicCountingRows unconstrained
    withoutClasses = Map.map (map ([] <$))

{- | The size classes of each state from the count table of unambiguous rows,
with the key of the row of each state.
-}
fromTable ::
    (Ord key, Ord symbol) =>
    Map.Map key [FTA.Transition key symbol Ordinary.EqualChildren] -> (state -> key) -> state -> Sized symbol
fromTable rows key = \state ->
    let index = indexOf (key state)
        count = countAtSize index
        unrank size (ClassRank rank)
            | rank >= 0 && Cardinality rank < count size =
                Just $ rankedValue $ sizeClassSelect index size (ClassRank rank)
            | otherwise = Nothing
        position = Ordinary.tablePosition (key state) rows
     in Sized
            { sizedTermsFrom = \size (ClassRank from) ->
                let Cardinality total = count size
                 in [term | rank <- [max 0 from .. total - 1], Just term <- [unrank size (ClassRank rank)]]
            , sizedCount = count
            , sizedUnrank = unrank
            , sizedRank = fmap (\(SizedRank size rank) -> (size, rank)) . position
            }
  where
    indexOf = Ordinary.tableIndexes rows

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
    rows = Ordinary.sortedRows automaton

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
    rows = Ordinary.sortedRows automaton
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
        { sizedTermsFrom = \size (ClassRank from) -> genericDrop from $ classOf size
        , sizedCount = Cardinality . genericLength . classOf
        , sizedUnrank = \size (ClassRank rank) ->
            if rank < 0 then Nothing else listToMaybe $ genericDrop rank $ classOf size
        , sizedRank = \term ->
            let size = Size $ toInteger $ length term
             in (,) size . ClassRank . toInteger <$> elemIndex term (classOf size)
        }

-- | The distinct accepted terms with the given number of nodes, in order.
termsOfSize :: Sized symbol -> Size -> [Term symbol]
termsOfSize classes size = sizedTermsFrom classes size 0

{- | The terms of a size class from a class rank on, in order. The list skips
the terms before the class rank without building them where the count table
applies. A negative class rank gives the whole class.
-}
termsOfSizeFrom :: Sized symbol -> Size -> ClassRank -> [Term symbol]
termsOfSizeFrom = sizedTermsFrom

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
