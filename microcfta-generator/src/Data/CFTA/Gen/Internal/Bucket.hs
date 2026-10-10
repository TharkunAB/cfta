{- | Retained key groups of finite languages.

A t'KeyedBucket' is one finite language and its mass in the whole
distribution. Grouping, application, and relation all produce buckets, so the
merge that normalizes them is written once here.
-}
module Data.CFTA.Gen.Internal.Bucket (
    KeyedBucket (..),
    groupOutcomes,
    bucketFromOutcomes,
    mergeBucketGroup,
    mergeComponentsByKey,

    -- * Masses
    bucketMassIndex,
    MassIndex (..),
    massAtSize,
    emptyMassIndex,
    countMassIndex,
    atomicMassIndex,
    sumMassIndexes,
    productMassIndex,
    payMassIndex,
) where

import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support (singletonNode)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Ranked.Internal.Decoder (MinimumSize (..), Plan (..), SizeIndex (minimumMemberSize))
import Data.CFTA.Ranked.Internal.Sampler (atomicSampleIndex)
import qualified Data.CFTA.Term as Term
import Data.CFTA.Ranked.Internal.Size (sizeClassCounts, addSparse, mulSparse, valueAtSize, fromMinimum, payMinimum)

-- | One compact conditional generator and its mass in the whole distribution.
data KeyedBucket symbol a = KeyedBucket
    { keyedBucketMass :: !Rational
    , keyedBucketStatic :: !(Static symbol a)
    , keyedBucketMasses :: !(Maybe MassIndex)
    {- ^ The weight of the group in each size class, on the scale of member
    counts, when it is not the member count of the class. A group that keeps
    some members of a language keeps their weights in that language here, so
    a merge chooses it inside a size class by these weights. 'Nothing' means
    the member counts.
    -}
    }

-- | Group enumerated outcomes by key, in their order.
groupOutcomes :: (Ord key) => [(key, outcome)] -> Map.Map key (Seq outcome)
groupOutcomes = Map.fromListWith (flip (<>)) . map (fmap Sequence.singleton)

{- | Build one retained group from its outcomes, in rank order.

Every outcome comes with the weight of its rank inside its size class in the
grouped language, as 'enumerateWeighted' gives it. Every member of a group
has size one, and the members keep their weights relative to each other, so
an atomic choice inside the grouped language keeps its distribution inside
the group.
-}
bucketFromOutcomes ::
    (Hashable symbol, Typeable symbol) =>
    Bool -> Seq (Rational, Outcome symbol a) -> Either GenError (KeyedBucket symbol a)
bucketFromOutcomes retainAtomic weightedOutcomes = do
    sampler <- sequenceSampler conditional
    sizeSampling <- case commonValue $ toList $ Just . fst <$> weightedOutcomes of
        Just _ -> pure Nothing
        Nothing -> do
            weightSampler <-
                sequenceSampler $
                    (\(weight, outcome) -> outcome{outcomeMass = weight}) <$> weightedOutcomes
            pure $ Just (atomicSampleIndex 1 weightSampler, Right . weightAt)
    let static = Static
            bucketSupport
            ( mkOutcomeIndex
                totalOutcomes
                uniformMass
                select
                (enumeratedRanks $ toList $ outcomeTerm <$> outcomes)
                selectValue
                sampler
                (PlanSelect totalOutcomes selectValue)
            )
                { outcomeSizeSampling = sizeSampling
                }
            retainAtomic
            (Inspection Nothing $ Node [rootEdge $ outcomeInspection outcome | outcome <- toList outcomes])
            (commonRootCount $ toList $ RootCount . termRootCount . outcomeTerm <$> outcomes)
    pure $ KeyedBucket bucketMass static Nothing
  where
    outcomes = snd <$> weightedOutcomes
    -- The weights of the group add up to its number of members.
    weights = fst <$> weightedOutcomes
    totalWeight = sum weights
    weightAt index =
        toRational totalOutcomes * Sequence.index weights (fromEnum index) / totalWeight
    bucketMass = sum $ outcomeMass <$> outcomes
    conditional = (\outcome -> outcome{outcomeMass = outcomeMass outcome / bucketMass}) <$> outcomes
    totalOutcomes = toEnum $ length outcomes
    uniformMass = commonValue $ Just . outcomeMass <$> toList conditional
    bucketSupport = Node [rootEdge $ outcomeTerm outcome | outcome <- toList outcomes]
    rootEdge (Term.Node symbol children) = Edge symbol $ map singletonNode children

    select index = do
        checkIndex totalOutcomes index
        pure $ Sequence.index conditional $ fromEnum index

    selectValue = outcomeValue . Sequence.index conditional . fromEnum

-- | Merge weighted buckets into one group.
mergeBucketGroup ::
    (Hashable symbol, Typeable symbol) =>
    [KeyedBucket symbol a] -> Either GenError (KeyedBucket symbol a)
-- One bucket is already the group, and rebuilding it through
-- 'frequencyStatic' would drop its atomic marker.
mergeBucketGroup [bucket] | keyedBucketMass bucket > 0 = Right bucket
mergeBucketGroup buckets = do
    weighted <- integerOutcomes [(keyedBucketMass bucket, bucket) | bucket <- buckets]
    pure $ KeyedBucket (sum $ map keyedBucketMass buckets) (merged weighted) masses
  where
    massWeighted = any (isJust . keyedBucketMasses) buckets
    merged weighted
        -- A bucket with weights of its own is chosen by them inside a size class.
        | massWeighted =
            frequencyStaticWithMasses
                [(weight, massAtSize <$> keyedBucketMasses bucket, keyedBucketStatic bucket) | (weight, bucket) <- weighted]
        -- All-atomic alternatives have size-one plans, so their merge is
        -- still one source choice and stays atomic. A mixed merge is not.
        | otherwise = retainAtomic $ frequencyStatic [(weight, keyedBucketStatic bucket) | (weight, bucket) <- weighted]
    masses
        | massWeighted = Just $ sumMassIndexes $ map bucketMassIndex buckets
        | otherwise = Nothing
    retainAtomic
        | all (staticAtomic . keyedBucketStatic) buckets
        , first@(MinimumSize (Size size)) : rest <- map (minimumMemberSize . outcomeSizeIndex . staticOutcomes . keyedBucketStatic) buckets
        , all (== first) rest =
            -- An atom has size one, and each pay above it adds one.
            \merged -> iterate payStatic (atomicStatic merged) !! fromInteger (size - 1)
        | otherwise = id

-- | Merge weighted joined components into normalized result-key groups.
mergeComponentsByKey ::
    (Ord resultKey, Hashable symbol, Typeable symbol) =>
    [(resultKey, KeyedBucket symbol a)] ->
    Either GenError (Map.Map resultKey (KeyedBucket symbol a))
mergeComponentsByKey [] = Left EmptyGenerator
mergeComponentsByKey components = do
    unnormalized <- traverse (mergeBucketGroup . toList) grouped
    let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
    pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    grouped = groupOutcomes components

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }

-- | The weight of a bucket in each size class: its own weights, or its member counts.
bucketMassIndex :: KeyedBucket symbol a -> MassIndex
bucketMassIndex bucket =
    fromMaybe (countMassIndex $ outcomeSizeIndex $ staticOutcomes $ keyedBucketStatic bucket) $ keyedBucketMasses bucket

{- | A memoized unnormalized mass for sizes in ascending order. Sizes without
members are left out. A product and a pay start at their minimum size.
-}
newtype MassIndex = MassIndex [(Size, Rational)]

-- | Read one size, returning zero outside the sizes with mass.
massAtSize :: MassIndex -> Size -> Rational
massAtSize (MassIndex masses) = valueAtSize masses

-- | A language with no members at any size.
emptyMassIndex :: MassIndex
emptyMassIndex = MassIndex []

-- | Structural counts interpreted as unnormalized uniform mass.
countMassIndex :: SizeIndex a -> MassIndex
countMassIndex index =
    MassIndex [(size, toRational count) | (size, count) <- sizeClassCounts index]

-- | One finite atom's complete mass at its size.
atomicMassIndex :: Size -> Rational -> MassIndex
atomicMassIndex size mass = MassIndex [(size, mass) | mass > 0]

-- | Add alternative masses by size.
sumMassIndexes :: [MassIndex] -> MassIndex
sumMassIndexes indexes = MassIndex $ foldr (\(MassIndex masses) -> addSparse masses) [] indexes

{- | Convolve two mass series: the sizes of a pair add, and the masses
multiply. The masses start with the smallest size of the product, the sum of
the minimum sizes of its sides, before the convolution is read, as the size
counts of a product do. So a recursive knot of masses gives its smallest sizes
before the product is computed.
-}
productMassIndex :: MinimumSize -> MassIndex -> MassIndex -> MassIndex
productMassIndex smallest (MassIndex left) (MassIndex right) =
    MassIndex $ fromMinimum smallest $ mulSparse left right

{- | The masses of a pay: each size is one larger. Given the minimum size of
the inner language, the masses start with its smallest size before the inner
masses are read, as the counts of a pay do.
-}
payMassIndex :: MinimumSize -> MassIndex -> MassIndex
payMassIndex smallest (MassIndex masses) =
    MassIndex $ fromMinimum (payMinimum smallest) [(size + 1, mass) | (size, mass) <- masses]
