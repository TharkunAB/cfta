{-# LANGUAGE OverloadedStrings #-}

{- | Resume a size-ordered listing of the terms of a graph, or a sampled run of
draws from that listing, also in a new process.

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
edited graph. 'resume' compares the two graphs row by row. A new order of the
transitions of one state also makes a checkpoint stale: the ranks of a size
class follow the order of the rows (ADR 4), so the new order can change the
listing.

'relocate' finds a term in a graph and gives a checkpoint at that term. Use it
only when you want to continue in an edited graph. It does not continue the
old listing: the new listing can repeat or skip terms of the old one.

A sampled run draws terms from the same listing. 'startSampling' gives the
checkpoint before the first draw, and 'resumeSampling' gives the draws from a
checkpoint on, each with the checkpoint after it. Draw @i@ is a function of
the seed and of @i@ only, so a sampling checkpoint holds the seed and the
number of draws, and no state of the pseudorandom generator. Without weights,
each term of the listing has the same chance. With weights, a draw selects a
size by its weight, then a term of that size with the same chance for each.
'resumeSampling' rejects a checkpoint of another graph or of other weights.
The bound and the seed come from the checkpoint.

The routes decide equality constraints without a solver. A guard beyond
equality constraints needs a solver. 'resume', 'relocate', and
'resumeSampling' reject a graph with such a guard: the result is
'QueryFailed' 'Data.CFTA.Sized.ResidualGuard'.
-}
module Data.CFTA.Sized.Checkpoint (
    Checkpoint (..),
    CheckpointError (..),
    route,
    routeVersion,
    start,
    resume,
    relocate,

    -- * Sampling
    SamplingCheckpoint (..),
    sampleRoute,
    sampleRouteVersion,
    prng,
    prngVersion,
    startSampling,
    resumeSampling,
    splitMix64,
) where

import Control.Monad (forM_, when)
import Data.Bifunctor (first)
import Data.Bits (bit, shiftR, xor, (.&.))
import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Data.Word (Word64)

import qualified Data.CFTA as FTA
import Data.CFTA.Checkpoint (Checkpoint (..), SamplingCheckpoint (..))
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size, Weight (..))
import Data.CFTA.Sized (Sized, SizedError, countOfSize, rankOfSize, sized, termsOfSizeFrom, unrankOfSize)
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
    | -- | The sampling checkpoint has another pseudorandom generator, or another version of it.
      UnknownPrng !Text !Integer
    | -- | The weights are not the weights of the sampling checkpoint.
      StaleWeights
    | -- | A weight below one, or a weight of a size outside the listing.
      InvalidWeight !Size !Weight
    | -- | No term of the listing has a weight.
      NothingToDraw
    | -- | The number of draws of the sampling checkpoint is negative.
      InvalidDraws !Integer
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
    known UnknownRoute (route, routeVersion) (checkpointRoute checkpoint, checkpointVersion checkpoint)
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
    known UnknownRoute (route, routeVersion) (checkpointRoute checkpoint, checkpointVersion checkpoint)
    classes <- first QueryFailed $ sized graph
    case rankOfSize classes term of
        Just next@(size, _)
            | size <= checkpointBound checkpoint -> Right checkpoint{checkpointGraph = graph, checkpointNext = next}
        _ -> Left $ MissingTerm term

-- | The name of the sampling route: draws from the listing of 'route'.
sampleRoute :: Text
sampleRoute = "sized-sample"

{- | The version of the sampling route. Increase it when the order of
"Data.CFTA.Sized" changes, or when a draw uses the words of its stream in
another way.
-}
sampleRouteVersion :: Integer
sampleRouteVersion = 1

-- | The name of the pseudorandom generator: 'splitMix64'.
prng :: Text
prng = "splitmix64"

-- | The version of the pseudorandom generator. Increase it when 'splitMix64' changes.
prngVersion :: Integer
prngVersion = 1

{- | The sampling checkpoint before the first draw from the listing of the
terms up to a size bound, with the weights of the sizes, or 'Nothing' for the
same chance for each term, and a seed.
-}
startSampling :: Size -> Maybe (Map Size Weight) -> Word64 -> FTA.PlainFTA state Symbol -> SamplingCheckpoint state
startSampling bound weights seed graph =
    SamplingCheckpoint graph sampleRoute sampleRouteVersion bound weights prng prngVersion seed 0

{- | The draws from the next draw of a sampling checkpoint on, each with the
sampling checkpoint after it. The list has no end. The graph and the weights
must be those of the checkpoint.

Without weights, draw @i@ selects a rank of the listing below the number of
its terms, and gives the term at that rank. With weights, draw @i@ selects a
size by its weight, then a class rank below the number of terms of that size.
A size with no terms is not selected. Each weight must be at least one, and
its size must be from one to the bound. Both selections read the words of
the stream of draw @i@ (see 'splitMix64'), in order.
-}
resumeSampling ::
    (Ord state) =>
    SamplingCheckpoint state ->
    FTA.PlainFTA state Symbol ->
    Maybe (Map Size Weight) ->
    Either (CheckpointError state) [(Term Symbol, SamplingCheckpoint state)]
resumeSampling checkpoint graph weights = do
    known UnknownRoute (sampleRoute, sampleRouteVersion) (samplingRoute checkpoint, samplingVersion checkpoint)
    known UnknownPrng (prng, prngVersion) (samplingPrng checkpoint, samplingPrngVersion checkpoint)
    maybe (Right ()) Left $ staleness (samplingGraph checkpoint) graph
    when (samplingWeights checkpoint /= weights) $ Left StaleWeights
    classes <- first QueryFailed $ sized graph
    select <- selection classes (samplingBound checkpoint) weights
    let draws = samplingDraws checkpoint
    when (draws < 0) $ Left $ InvalidDraws draws
    pure
        [ (term, checkpoint{samplingDraws = index + 1})
        | index <- [draws ..]
        , let (size, rank) = select $ drawStream (samplingSeed checkpoint) index
              term = maybe (error "cfta-generator bug: a draw outside its size class") id $ unrankOfSize classes size rank
        ]

{- | The selection of a sized rank from the words of a stream, or the reason
why the listing has nothing to draw.
-}
selection ::
    Sized Symbol -> Size -> Maybe (Map Size Weight) -> Either (CheckpointError state) ([Word64] -> (Size, ClassRank))
selection classes bound weights = case weights of
    Nothing -> do
        let counted = [(size, count) | size <- [1 .. bound], let Cardinality count = countOfSize classes size, count > 0]
            total = sum $ map snd counted
            offsets = Map.fromList $ zip (scanl (+) 0 $ map snd counted) counted
        when (total == 0) $ Left NothingToDraw
        pure $ \stream ->
            let (rank, _) = below total stream
                (offset, (size, _)) = atOffset rank offsets
             in (size, ClassRank $ rank - offset)
    Just weighted -> do
        forM_ (Map.toAscList weighted) $ \(size, Weight weight) ->
            when (weight < 1 || size < 1 || size > bound) $ Left $ InvalidWeight size (Weight weight)
        let drawn =
                [ (size, (weight, count))
                | (size, Weight weight) <- Map.toAscList weighted
                , let Cardinality count = countOfSize classes size
                , count > 0
                ]
            total = sum $ map (fst . snd) drawn
            offsets = Map.fromList $ zip (scanl (+) 0 $ map (fst . snd) drawn) drawn
        when (total == 0) $ Left NothingToDraw
        pure $ \stream ->
            let (ticket, rest) = below total stream
                (_, (size, (_, count))) = atOffset ticket offsets
                (rank, _) = below count rest
             in (size, ClassRank rank)

-- | The entry with the largest offset at most the value. The offsets start at zero.
atOffset :: Integer -> Map Integer entry -> (Integer, entry)
atOffset value offsets = maybe (error "cfta-generator bug: a value below the first offset") id $ Map.lookupLE value offsets

{- | An integer from zero to below a bound of at least one, from the words of
a stream, and the rest of the stream.

A value takes as many words as the bound needs, the first word lowest, and
keeps the bits that the bound needs. A value at or above the bound is
rejected, and the next words give the next value. Thus each integer below the
bound has the same chance. A bound of one takes no words.
-}
below :: Integer -> [Word64] -> (Integer, [Word64])
below bound stream
    | bound <= 1 = (0, stream)
    | otherwise = go stream
  where
    bits = length $ takeWhile (> 0) $ iterate (`shiftR` 1) (bound - 1)
    count = (bits + 63) `div` 64
    go remaining =
        let (taken, rest) = splitAt count remaining
            value = foldr (\word higher -> higher * 2 ^ (64 :: Int) + toInteger word) 0 taken .&. (bit bits - 1)
         in if value < bound then (value, rest) else go rest

{- | The stream of draw @i@: the 'splitMix64' stream from word @i@ of the
'splitMix64' stream of the seed.
-}
drawStream :: Word64 -> Integer -> [Word64]
drawStream seed index = splitMix64 $ mix $ seed + golden * fromInteger (index + 1)

{- | The SplitMix64 stream from a state, as in @splitmix64.c@ of Sebastiano
Vigna (<https://prng.di.unimi.it/splitmix64.c>): each step adds the golden
gamma to the state and mixes the result. The stream from state zero starts
with @0xe220a8397b1dcdaf@.
-}
splitMix64 :: Word64 -> [Word64]
splitMix64 state = map mix $ drop 1 $ iterate (+ golden) state

-- | The golden gamma of SplitMix64.
golden :: Word64
golden = 0x9e3779b97f4a7c15

-- | The output function of @splitmix64.c@.
mix :: Word64 -> Word64
mix state = third `xor` (third `shiftR` 31)
  where
    second = (state `xor` (state `shiftR` 30)) * 0xbf58476d1ce4e5b9
    third = (second `xor` (second `shiftR` 27)) * 0x94d049bb133111eb

-- | Reject another name or another version of a route or of a pseudorandom generator.
known ::
    (Text -> Integer -> CheckpointError state) -> (Text, Integer) -> (Text, Integer) -> Either (CheckpointError state) ()
known unknown expected (name, version)
    | (name, version) == expected = Right ()
    | otherwise = Left $ unknown name version

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
