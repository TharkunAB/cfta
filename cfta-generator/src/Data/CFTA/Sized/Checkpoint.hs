{-# LANGUAGE OverloadedStrings #-}

{- | Resume a size-ordered listing of the terms of a graph, also in a new
process.

The listing holds the terms of each size from one to a bound, in the order of
"Data.CFTA.Sized". 'start' gives the checkpoint before the first term.
'resume' gives the terms from a checkpoint on, each with the checkpoint after
it. Save one of these checkpoints. Later, 'resume' it for the terms after it,
in the same order. The text form @checkpoint 1;@ of @cfta-serialization@ saves
a checkpoint with its graph.

'resume' builds the size classes of the graph again, so it needs no state of
an earlier process. It rejects a checkpoint of another route, of another
version of the route, or of another graph. An edit to a graph can change the
order of its terms. Thus the position of a checkpoint has no meaning in an
edited graph. 'resume' compares the two graphs row by row, so a new order of
the transitions of one state also makes a checkpoint stale.

'relocate' finds a term in a graph and gives a checkpoint at that term. Use it
only when you want to continue in an edited graph. It does not continue the
old listing: the new listing can repeat or skip terms of the old one.

The route decides equality constraints without a solver. A guard beyond
equality constraints needs a solver. 'resume' and 'relocate' reject a graph
with such a guard: the result is 'QueryFailed' 'Data.CFTA.Sized.ResidualGuard'.
-}
module Data.CFTA.Sized.Checkpoint (
    Checkpoint (..),
    CheckpointError (..),
    route,
    routeVersion,
    start,
    resume,
    relocate,
) where

import Control.Monad (when)
import Data.Bifunctor (first)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Text (Text)

import qualified Data.CFTA as FTA
import Data.CFTA.Checkpoint (Checkpoint (..))
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size)
import Data.CFTA.Sized (SizedError, countOfSize, rankOfSize, sized, termsOfSizeFrom)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)

-- | Why a checkpoint does not resume, or does not relocate.
data CheckpointError state
    = -- | The checkpoint has another route, or another version of the route.
      UnknownRoute !Text !Integer
    | -- | The initial state of the graph of the checkpoint, and the other initial state of the graph.
      StaleStart !state !state
    | -- | The first state whose row is not the same in the graph of the checkpoint and in the graph.
      StaleRow !state
    | -- | The route cannot build the size classes of the graph.
      QueryFailed !SizedError
    | -- | No term of the listing has this sized rank, and it is not the end of a size class of the listing.
      OutsideListing !Size !ClassRank
    | -- | The graph does not accept the term, or the term is larger than the bound.
      MissingTerm !(Term Symbol)
    deriving (Eq, Show)

-- | The name of the route: the order of "Data.CFTA.Sized".
route :: Text
route = "sized"

-- | The version of the route. Increase it when the order of "Data.CFTA.Sized" changes.
routeVersion :: Integer
routeVersion = 1

-- | The checkpoint before the first term of the listing of the terms up to a size bound.
start :: Size -> FTA.PlainFTA state Symbol -> Checkpoint state
start bound graph = Checkpoint graph route routeVersion bound (1, 0)

{- | The terms of the listing from the next term of a checkpoint on, each with
the checkpoint after it. The graph must be the graph of the checkpoint.

The next term of a checkpoint has a size of at least one, and a class rank
from zero to the number of terms of that size in the listing. A class rank
equal to that number is the end of the size class, and the listing continues
with the next size. A size class above the bound is empty in the listing.
-}
resume ::
    (Ord state) =>
    Checkpoint state -> FTA.PlainFTA state Symbol -> Either (CheckpointError state) [(Term Symbol, Checkpoint state)]
resume checkpoint graph = do
    knownRoute checkpoint
    maybe (Right ()) Left $ staleness (checkpointGraph checkpoint) graph
    classes <- first QueryFailed $ sized graph
    let bound = checkpointBound checkpoint
        (size, ClassRank rank) = checkpointNext checkpoint
        Cardinality listed = if size <= bound then countOfSize classes size else 0
    when (size < 1 || rank < 0 || rank > listed) $ Left $ OutsideListing size (ClassRank rank)
    pure
        [ (term, checkpoint{checkpointNext = (at, after)})
        | (at, from) <- (size, ClassRank rank) : [(later, 0) | later <- [size + 1 .. bound]]
        , at <= bound
        , (after, term) <- zip [from + 1 ..] (termsOfSizeFrom classes at from)
        ]

{- | A checkpoint of the same query on a graph, at a term. Resuming it gives
the term first.

This does not continue the listing of the old checkpoint. The listing of the
graph can repeat or skip terms of the old listing. The result is
'MissingTerm' when the graph does not accept the term, or when the term is
larger than the bound.
-}
relocate ::
    (Ord state) =>
    Checkpoint state -> FTA.PlainFTA state Symbol -> Term Symbol -> Either (CheckpointError state) (Checkpoint state)
relocate checkpoint graph term = do
    knownRoute checkpoint
    classes <- first QueryFailed $ sized graph
    case rankOfSize classes term of
        Just next@(size, _)
            | size <= checkpointBound checkpoint -> Right checkpoint{checkpointGraph = graph, checkpointNext = next}
        _ -> Left $ MissingTerm term

-- | Reject a checkpoint of another route or of another version of the route.
knownRoute :: Checkpoint state -> Either (CheckpointError state) ()
knownRoute Checkpoint{checkpointRoute, checkpointVersion}
    | checkpointRoute == route && checkpointVersion == routeVersion = Right ()
    | otherwise = Left $ UnknownRoute checkpointRoute checkpointVersion

{- | The first difference between the graph of a checkpoint and another graph:
the initial state, then the rows in state order. 'Nothing' when the graphs
are equal.
-}
staleness :: (Ord state) => FTA.PlainFTA state Symbol -> FTA.PlainFTA state Symbol -> Maybe (CheckpointError state)
staleness saved graph
    | FTA.initialState saved /= FTA.initialState graph = Just $ StaleStart (FTA.initialState saved) (FTA.initialState graph)
    | otherwise = StaleRow <$> find differs (Map.keys $ Map.union savedRows rows)
  where
    savedRows = FTA.transitionTable saved
    rows = FTA.transitionTable graph
    differs state = Map.lookup state savedRows /= Map.lookup state rows
