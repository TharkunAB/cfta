{- | Backend-independent value and rank sampling.

This module is an exposed internal module. The generator layers of
cfta-generator use it directly. Its exports are not covered by the PVP
contract of the package.

A t'Sampler' is a plan, and each backend interprets the plan. The meaning of
a sampler is its distribution. With the t'Exact' backend, a field of a
sampler is the list of the outcomes with their probabilities, and
'exactPmfAtSize' reads that list. The compiled data and the tables of this
module do not change a distribution. They change only the work and the
memory of a draw.

A field of a t'Sampler' is a function of the backend. Thus a value that a
field computes is computed again at each use of the field, unless the value
is bound outside the field. For this reason, the combinators of a recursive
language keep their data outside the fields:

* A choice or a product compiles its alternatives one time for each size
  class (@Alternatives@). The compiled alternatives hold the weights, the
  ticket table of the weights ('compileTickets'), and the samplers of the
  parts. The two fields of the sampler share them.

* A choice or a product keeps the sampler of each size class in a table
  (@memoSampleIndex@). The lowering of a generator applies a combinator one
  time for each node of the generator, so each node has one table.

A draw makes one selection at each node that it visits
('selectAlternative'), and it builds only the generator of the selected
alternative. The memory of a sampler has a bound that the generator and the
largest requested size give. The count of the draws does not change the
bound.

The functions of this module obey these laws. The selection law and the law
of the compiled alternatives are equalities of distributions, and they hold
for every backend. With t'Exact', the two sides are the same list of
outcomes.

* Selection: for one or more positive weights,
  @selectAlternative weights (compileTickets weights) run@ is
  @frequencyGen (zip weights (map run [0 ..]))@.

* Ticket table: for the positive weights @w0@ to @wn@, 'compileTickets'
  gives the total @w0 + .. + wn@. For each ticket @t@ from zero and below
  the total, it gives the smallest position @i@ with @t < w0 + .. + wi@.

* Compiled alternatives:
  @chooseAlternative (countAlternatives [(weight, x)]) run@ is @run x@. For
  two or more alternatives,
  @chooseAlternative (countAlternatives weighted) run@ is
  @frequencyGen [(weight, run x) | (weight, x) <- weighted]@. And
  @massAlternatives weighted@ is @countAlternatives (integerMasses live)@,
  where @live@ holds the alternatives of @weighted@ that have a positive
  mass. As a precondition, the list of the alternatives is not empty, each
  weight is positive, and one mass at least is positive.

* Memo: @samplerAtSize (memoSampleIndex build) size@ is @build size@.
-}
module Data.CFTA.Ranked.Internal.Sampler (
    GenBackend (..),
    Exact (..),
    Sampler (..),
    SampleIndex (..),
    atomicSampleIndex,
    boundedMassSampler,
    boundedSampler,
    choiceMassSampleIndex,
    choiceSampleIndex,
    compileTickets,
    compileWeighted,
    emptySampleIndex,
    exactPmfAtSize,
    fixSampleIndex,
    integerMasses,
    mapSampleIndex,
    mapSampler,
    paySampleIndex,
    productMassSampleIndex,
    productSampleIndex,
    productSampler,
    uniformSampleIndex,
    uniformSampler,
) where

import Data.List (genericIndex, mapAccumL)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import GHC.Arr (Array, listArray, unsafeAt, (!))

import Data.CFTA.Index (
    Cardinality (..),
    ClassRank (..),
    Rank (..),
    RankOffset,
    Size (..),
    Weight (..),
    countWeight,
    everyRank,
    nextOffset,
    offsetRank,
    pairRank,
 )
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..), SizeClass (..), offsetRankedValue, withOffsets)
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex,
    countAtSize,
    sizeClassCounts,
    sizeClassSelect,
 )

-- | Operations a sampling backend provides.
class (Applicative gen) => GenBackend gen where
    -- | Select a rank of a language with the given cardinality, in @[0, cardinality)@.
    selectInteger :: Cardinality -> gen Rank

    -- | Select a machine 'Int' in @[0, bound)@.
    selectInt :: Int -> gen Int
    selectInt bound = (\(Rank rank) -> fromInteger rank) <$> selectInteger (Cardinality $ toInteger bound)

    -- | Select one backend generator with a positive relative weight.
    frequencyGen :: [(Weight, gen a)] -> gen a

    {- | Select one of the weighted values through its compiled ticket table.

    The default draws one ticket and decodes it. A backend that enumerates
    outcomes reads the weights instead, so it gives one outcome for each value
    and not one for each ticket.
    -}
    selectWeighted :: [(Weight, a)] -> (Int, Int -> a) -> gen a
    selectWeighted _ (bound, decode) = decode <$> selectInt bound

    {- | Select one alternative by weight, then run the generator of that
    alternative.

    The alternatives are the positions from zero. The list gives the positive
    weight of each position. The pair is the ticket table that
    'compileTickets' gives for these weights: the count of the tickets, and
    the position that holds each ticket. The function gives the generator of
    a position.

    The result has the distribution of the default, which is 'frequencyGen'
    on the generators of all the positions. A backend that draws one outcome
    overrides the default: it draws one ticket, and it builds only the
    generator of the position that holds the ticket. Thus the backend keeps
    no generator of an alternative after a draw.
    -}
    selectAlternative :: [Weight] -> (Integer, Integer -> Int) -> (Int -> gen a) -> gen a
    selectAlternative weights _ run = frequencyGen $ zip weights $ map run [0 ..]

-- | A finite exact interpretation of one sampler, for distribution checks.
newtype Exact a = Exact {runExact :: [(Rational, a)]}

instance Functor Exact where
    fmap transform (Exact outcomes) =
        Exact [(mass, transform value) | (mass, value) <- outcomes]

instance Applicative Exact where
    pure value = Exact [(1, value)]
    Exact functions <*> Exact values =
        Exact
            [ (functionMass * valueMass, function value)
            | (functionMass, function) <- functions
            , (valueMass, value) <- values
            ]

instance GenBackend Exact where
    selectInteger cardinality@(Cardinality count) =
        Exact
            [ (1 / fromInteger count, rank)
            | rank <- everyRank cardinality
            ]

    frequencyGen alternatives =
        Exact
            [ (toRational weight / toRational totalWeight * mass, value)
            | (weight, Exact outcomes) <- alternatives
            , (mass, value) <- outcomes
            ]
      where
        totalWeight = sum $ map fst alternatives

    -- One outcome for each value: enumerating the tickets would multiply the
    -- outcomes of a product by the ticket count of every draw.
    selectWeighted weighted _ =
        Exact [(toRational weight / toRational totalWeight, value) | (weight, value) <- weighted]
      where
        totalWeight = sum $ map fst weighted

-- | Backend-independent plans for sampling a value, with or without its rank.
data Sampler a = Sampler
    { runValueSampler :: forall gen. (GenBackend gen) => gen a
    , runRankSampler :: forall gen. (GenBackend gen) => gen (RankedValue a)
    }

{- | The sampler for each recursive size class.

Its rank is a position in that class, not a global rank. The bounded sampler
adds the preceding size classes to recover the stable size-major rank.
-}
newtype SampleIndex a = SampleIndex
    { samplerAtSize :: Size -> Sampler a
    }

-- | Sample one value of the given size class.
runValueAtSize :: (GenBackend gen) => SampleIndex a -> Size -> gen a
runValueAtSize sampling = runValueSampler . samplerAtSize sampling

{- | Aggregate the exact value distribution of one recursive size class.

This interprets the sampler rather than its structural ranks, so weighted
finite choices closed with @atomic@ keep their declared probability. The
observer may enumerate a sampler's products and is intended for diagnostics,
not for large language hot paths.
-}
exactPmfAtSize :: (Ord a) => SampleIndex a -> Size -> [(a, Rational)]
exactPmfAtSize sampling size =
    Map.toAscList
        $ Map.fromListWith (+)
        $ [(value, mass) | (mass, value) <- runExact $ runValueAtSize sampling size]

-- | Map sampled values while keeping their ranks.
mapSampler :: (a -> b) -> Sampler a -> Sampler b
mapSampler transform sampler =
    Sampler
        (transform <$> runValueSampler sampler)
        (fmap transform <$> runRankSampler sampler)

-- | Sample uniformly with one selection, using a machine 'Int' when it fits.
uniformSampler :: Cardinality -> (Rank -> a) -> Sampler a
uniformSampler 1 valueAt = Sampler (pure $ valueAt 0) (pure $ RankedValue 0 (valueAt 0))
uniformSampler (Cardinality totalOutcomes) valueAt
    | totalOutcomes <= toInteger (maxBound :: Int) =
        let bound = fromInteger totalOutcomes
            rankOfInt = Rank . toInteger
            valueAtInt = valueAt . rankOfInt
         in Sampler
                (valueAtInt <$> selectInt bound)
                ((\index -> RankedValue (rankOfInt index) (valueAtInt index)) <$> selectInt bound)
uniformSampler totalOutcomes valueAt =
    Sampler
        (valueAt <$> selectInteger totalOutcomes)
        ((\rank -> RankedValue rank (valueAt rank)) <$> selectInteger totalOutcomes)

-- | Sample a product, composing ranks in mixed radix.
productSampler :: Cardinality -> Sampler (a -> b) -> Sampler a -> Sampler b
productSampler rightCardinality leftSampler rightSampler =
    Sampler
        (runValueSampler leftSampler <*> runValueSampler rightSampler)
        ( liftA2
            ( \(RankedValue leftRank partial) (RankedValue rightRank value) ->
                RankedValue (pairRank rightCardinality leftRank rightRank) (partial value)
            )
            (runRankSampler leftSampler)
            (runRankSampler rightSampler)
        )

-- | Uniformly sample a position from one counted size class.
uniformSampleIndex :: SizeIndex a -> SampleIndex a
uniformSampleIndex index =
    SampleIndex $ \size ->
        -- The ranks of this sampler are the positions in the size class.
        uniformSampler
            (countAtSize index size)
            (\(Rank position) -> rankedValue $ sizeClassSelect index size $ ClassRank position)

-- | Use one finite atomic sampler as the only size class, of the given size.
atomicSampleIndex :: Size -> Sampler a -> SampleIndex a
atomicSampleIndex atomSize sampler =
    SampleIndex $ \size -> if size == atomSize then sampler else wrongSize size
  where
    wrongSize size =
        error $
            "cfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.atomicSampleIndex: "
                <> "an atom has no members of size "
                <> show size

-- | The samplers of a pay: each size class is the class one smaller of the inner language.
paySampleIndex :: SampleIndex a -> SampleIndex a
paySampleIndex sampling = SampleIndex $ \size -> samplerAtSize sampling (size - 1)

-- | A placeholder for an empty recursive language. It is never sampled.
emptySampleIndex :: SampleIndex a
emptySampleIndex =
    SampleIndex $ const unavailable
  where
    unavailable =
        error $
            "cfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.emptySampleIndex: "
                <> "an empty language has no members to sample"

-- | Map sampled values while keeping their size-class positions.
mapSampleIndex :: (a -> b) -> SampleIndex a -> SampleIndex b
mapSampleIndex transform sampling =
    SampleIndex $ mapSampler transform . samplerAtSize sampling

{- | The alternatives of one choice at one size class, compiled for selection.

The value is data and does not depend on a backend. A sampler of a recursive
language keeps one such value for each size class, and builds the generator
of an alternative only when a draw selects that alternative. An alternative
of a choice or of a product holds the samplers of its parts.
-}
data Alternatives alternative
    = -- | One alternative. The choice draws no ticket.
      OneAlternative alternative
    | {- | Two or more alternatives: the weight of each position, the ticket
      table of these weights, and the alternative at each position.
      -}
      ManyAlternatives [Weight] (Integer, Integer -> Int) (Array Int alternative)

-- | Compile alternatives with positive integer weights, such as member counts.
countAlternatives :: [(Weight, alternative)] -> Alternatives alternative
countAlternatives [(_, alternative)] = OneAlternative alternative
countAlternatives weighted@(_ : _ : _) =
    ManyAlternatives weights (compileTickets weights) (listArray (0, length weighted - 1) (map snd weighted))
  where
    weights = map fst weighted
countAlternatives [] =
    error $
        "cfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.countAlternatives: "
            <> "no live alternative"

{- | Compile alternatives with exact rational masses. An alternative with no
positive mass is not selected. The other masses become the smallest
equivalent integer weights.
-}
massAlternatives :: [(Rational, alternative)] -> Alternatives alternative
massAlternatives weighted =
    case integerMasses [(mass, alternative) | (mass, alternative) <- weighted, mass > 0] of
        [] ->
            error $
                "cfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.massAlternatives: "
                    <> "no positive mass"
        live -> countAlternatives live

{- | Select one of the compiled alternatives, then run the generator of that
alternative. The function builds a generator from an alternative. It is
applied after the selection, to the selected alternative only.
-}
chooseAlternative :: (GenBackend gen) => Alternatives alternative -> (alternative -> gen a) -> gen a
chooseAlternative (OneAlternative alternative) run = run alternative
chooseAlternative (ManyAlternatives weights tickets alternatives) run =
    selectAlternative weights tickets (run . (alternatives !))

{- | Compile positive weights to a ticket table: the count of the tickets, and
the position that holds each ticket.

Position @i@ holds as many tickets as weight @i@. The tickets of one position
are consecutive, and the positions are in order: the first ticket of position
@i@ is the sum of the weights before @i@. A ticket is valid from zero to the
count less one.
-}
compileTickets :: [Weight] -> (Integer, Integer -> Int)
compileTickets weights = (total, \ticket -> pick ticket 0 lastIndex)
  where
    (total, upperBounds) = mapAccumL accumulateWeight 0 weights
    accumulateWeight before (Weight weight) = let upperBound = before + weight in (upperBound, upperBound)
    lastIndex = length upperBounds - 1
    table = listArray (0, lastIndex) upperBounds
    -- Search for the first position whose upper bound is above the ticket.
    -- The upper bounds do not decrease, so a binary search finds the
    -- position that a linear scan finds.
    pick :: Integer -> Int -> Int -> Int
    pick ticket low high
        | low == high = low
        | ticket < table ! middle = pick ticket low middle
        | otherwise = pick ticket (middle + 1) high
      where
        middle = low + (high - low) `quot` 2

-- | One non-empty size split of a product.
data ProductPart = ProductPart
    { partBlock :: !Cardinality
    -- ^ Members of the product contributed by this split.
    , partOffset :: !RankOffset
    -- ^ Position of the split's first member within the size class.
    , partFunctionSize :: !Size
    , partArgumentSize :: !Size
    , partArgumentCount :: !Cardinality
    -- ^ Radix for composing the two positions into one.
    }

{- | Sample a product at one exact size, choosing among the size splits with
the supplied weights.

Sampling inside each side is delegated to that side, so an atomic sampler can
remain non-uniform without changing product counts or positions, and the
weights choose only between splits, never within one.

The first argument compiles the weighted splits of one size class:
'countAlternatives' for weights that are counts, and 'massAlternatives' for
weights that are masses.
-}
productSampleIndexBy ::
    (forall alternative. [(weight, alternative)] -> Alternatives alternative) ->
    (ProductPart -> weight) ->
    SizeIndex (a -> b) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    SampleIndex a ->
    SampleIndex b
productSampleIndexBy compile weightOf indexF samplingF indexX samplingX =
    memoSampleIndex $ \size ->
        -- Both fields share the compiled splits of this size class. A split
        -- holds the samplers of its two sides.
        let splits =
                compile
                    [ ( weightOf part
                      ,
                          ( part
                          , samplerAtSize samplingF $ partFunctionSize part
                          , samplerAtSize samplingX $ partArgumentSize part
                          )
                      )
                    | part <- productSampleParts indexF indexX size
                    ]
         in Sampler
                ( chooseAlternative splits $ \(_, function, argument) ->
                    liftA2 ($) (runValueSampler function) (runValueSampler argument)
                )
                ( chooseAlternative splits $ \(part, function, argument) ->
                    liftA2
                        (combine (partOffset part) (partArgumentCount part))
                        (runRankSampler function)
                        (runRankSampler argument)
                )
  where
    combine offset argumentCount (RankedValue functionPosition function) (RankedValue argumentPosition argument) =
        RankedValue (offsetRank offset $ pairRank argumentCount functionPosition argumentPosition) (function argument)

-- | Sample a product at one exact size, weighting splits by member count.
productSampleIndex ::
    SizeIndex (a -> b) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    SampleIndex a ->
    SampleIndex b
productSampleIndex = productSampleIndexBy countAlternatives (countWeight . partBlock)

{- | Sample a product whose two sides are conditioned key groups.

The mass functions give each group's unnormalized probability mass at one
size. They choose among size splits without changing structural rank offsets.
-}
productMassSampleIndex ::
    SizeIndex (a -> b) ->
    (Size -> Rational) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    (Size -> Rational) ->
    SampleIndex a ->
    SampleIndex b
productMassSampleIndex indexF massF samplingF indexX massX samplingX =
    productSampleIndexBy massAlternatives splitMass indexF samplingF indexX samplingX
  where
    splitMass part = massF (partFunctionSize part) * massX (partArgumentSize part)

-- | Every non-empty size split of a product, with its position offset.
productSampleParts ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Size ->
    [ProductPart]
productSampleParts indexF indexX size = go 0 $ takeWhile ((<= size) . fst) (sizeClassCounts indexF)
  where
    go _ [] = []
    go offset ((functionSize, functionCount) : rest)
        | block <= 0 = go offset rest
        | otherwise =
            ProductPart block offset functionSize argumentSize argumentCount
                : go (nextOffset offset block) rest
      where
        argumentSize = size - functionSize
        argumentCount = countAtSize indexX argumentSize
        block = functionCount * argumentCount

{- | Sample ordered alternatives at one exact size, choosing with the supplied
weights.

Rank offsets always come from the structural counts, whatever the weights are:
an alternative that is skipped because its weight is zero still occupies its
positions in the size class. The weight function is handed that count so it
never has to recompute it.

The first argument compiles the weighted alternatives of one size class, as
for 'productSampleIndexBy'.
-}
choiceSampleIndexBy ::
    (forall alternative. [(weight, alternative)] -> Alternatives alternative) ->
    [(SizeIndex a, Cardinality -> Size -> Maybe weight, SampleIndex a)] ->
    SampleIndex a
choiceSampleIndexBy compile alternatives =
    memoSampleIndex $ \size -> choiceSampler $ compile $ parts size
  where
    parts size = go 0 alternatives
      where
        go _ [] = []
        go offset ((index, weightAt, sampling) : rest) =
            case weightAt count size of
                Just weight -> (weight, (offset, samplerAtSize sampling size)) : go (nextOffset offset count) rest
                Nothing -> go (nextOffset offset count) rest
          where
            count = countAtSize index size

-- | Sample ordered alternatives at one exact size, weighted by member count.
choiceSampleIndex :: [(SizeIndex a, SampleIndex a)] -> SampleIndex a
choiceSampleIndex alternatives =
    choiceSampleIndexBy
        countAlternatives
        [(index, liveCount, sampling) | (index, sampling) <- alternatives]
  where
    liveCount count _ = if count > 0 then Just (countWeight count) else Nothing

{- | Sample alternatives conditioned on one retained key.

Structural counts still define rank offsets. The supplied masses choose the
alternative, so regrouping does not erase a declared atomic distribution.
-}
choiceMassSampleIndex ::
    [(SizeIndex a, Size -> Rational, SampleIndex a)] ->
    SampleIndex a
choiceMassSampleIndex alternatives =
    choiceSampleIndexBy
        massAlternatives
        [(index, liveMass massAtSize, sampling) | (index, massAtSize, sampling) <- alternatives]
  where
    liveMass massAtSize count size
        | count <= 0 = Nothing
        | mass <= 0 = Nothing
        | otherwise = Just mass
      where
        mass = massAtSize size

-- | Tie a guarded recursive sampler alongside its recursive size index.
fixSampleIndex :: (SampleIndex a -> SampleIndex a) -> SampleIndex a
fixSampleIndex build = sampling
  where
    sampling = build sampling

{- | Build the sampler of each size class one time.

@samplerAtSize (memoSampleIndex build) size@ is @build size@. The sampler of a
size class from zero is built at the first request for that size class. Each
later request gets the same sampler, so all the draws share the compiled
alternatives of a size class.
-}
memoSampleIndex :: (Size -> Sampler a) -> SampleIndex a
memoSampleIndex build = SampleIndex atSize
  where
    samplers = map (build . Size) [0 ..]
    atSize size@(Size natural)
        | natural >= 0 = samplers `genericIndex` natural
        | otherwise = build size

-- | Sample one bounded size class, then recover its global size-major rank.
boundedSampler :: [SizeClass a] -> SampleIndex a -> Sampler a
boundedSampler classes sampling =
    choiceSampler $
        countAlternatives
            [ (countWeight count, (offset, samplerAtSize sampling size))
            | (offset, SizeClass{classSize = size, classCardinality = count}) <- withOffsets classCardinality classes
            ]

{- | Sample one bounded size class in proportion to its mass, then recover its
global size-major rank. The counts of the classes still give the rank offsets.
One class at least must have a positive mass.
-}
boundedMassSampler :: [(SizeClass a, Rational)] -> SampleIndex a -> Sampler a
boundedMassSampler classes sampling =
    choiceSampler $
        massAlternatives
            [ (mass, (offset, samplerAtSize sampling $ classSize sizeClass))
            | (offset, (sizeClass, mass)) <- withOffsets (classCardinality . fst) classes
            ]

{- | Select one of the compiled alternatives. An alternative is a sampler with
the rank offset of its first member. The two fields share the compiled
alternatives.
-}
choiceSampler :: Alternatives (RankOffset, Sampler a) -> Sampler a
choiceSampler alternatives =
    Sampler
        (chooseAlternative alternatives $ \(_, sampler) -> runValueSampler sampler)
        (chooseAlternative alternatives $ \(offset, sampler) -> offsetRankedValue offset <$> runRankSampler sampler)

{- | Convert rational masses to the smallest equivalent integer weights.

Precondition: every mass is positive. That is what makes the common factor at
least one, so the final division is well defined.
-}
integerMasses :: [(Rational, a)] -> [(Weight, a)]
integerMasses outcomes =
    zip
        (map (Weight . (`div` commonFactor)) unscaled)
        (map snd outcomes)
  where
    unscaled =
        [ numerator mass * (commonDenominator `div` denominator mass)
        | mass <- masses
        ]
      where
        commonDenominator = foldl lcm 1 $ map denominator masses

        masses = map fst outcomes
    commonFactor = foldl gcd 0 unscaled

{- | Compile positive integer tickets when their total fits a machine 'Int'.

Larger ticket spaces keep their existing compositional sampler.
-}
compileWeighted :: [(Weight, a)] -> Maybe (Int, Int -> a)
compileWeighted weighted
    | totalWeight > 0
    , totalWeight <= toInteger (maxBound :: Int) =
        let bound = fromInteger totalWeight
            entries = snd $ mapAccumL compileGroup 0 grouped
            lastIndex = length entries - 1
            table = listArray (0, lastIndex) entries
            -- Search the array without allocating a lookup result per ticket.
            lookupTicket ticket = go 0 lastIndex
              where
                go low high
                    | low == high =
                        let (lowerBound, (ticketWidth, values)) = unsafeAt table low
                         in unsafeAt values $ (ticket - lowerBound) `quot` ticketWidth
                    | otherwise =
                        let midpoint = low + (high - low + 1) `quot` 2
                            (lowerBound, _) = unsafeAt table midpoint
                         in if ticket < lowerBound
                                then go low (midpoint - 1)
                                else go midpoint high
         in Just (bound, lookupTicket)
    | otherwise = Nothing
  where
    Weight totalWeight = sum $ map fst weighted
    -- Prepending each singleton keeps grouping linear. Ticket order is
    -- private; every payload still carries its original structural rank.
    grouped =
        Map.toAscList $
            Map.fromListWith
                (<>)
                [(weight, [value]) | (weight, value) <- weighted]

    compileGroup lowerBound (Weight weight, values) =
        let !ticketWidth = fromInteger weight
            !upperBound = lowerBound + ticketWidth * length values
            !valueTable = listArray (0, length values - 1) values
         in ( upperBound
            , (lowerBound, (ticketWidth, valueTable))
            )
