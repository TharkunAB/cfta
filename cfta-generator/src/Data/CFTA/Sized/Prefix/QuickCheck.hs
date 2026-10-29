-- | QuickCheck generators of the completions of a prefix.
module Data.CFTA.Sized.Prefix.QuickCheck (
    sampleCompletion,
    sampleWeighted,
) where

import Data.Maybe (fromMaybe)
import Data.Ratio (denominator, numerator)
import qualified Test.QuickCheck as QC

import Data.CFTA.Index (Cardinality (..), Rank (..))
import Data.CFTA.Sized.Prefix (Completions, completionCount, drawCompletion, unrankCompletion)
import Data.CFTA.Term (Term)

{- | A generator of the completions, each with the same probability. It draws
a rank and unranks it, so the rank of a sample is known. 'Nothing' when there
is no completion.
-}
sampleCompletion :: Completions symbol -> Maybe (QC.Gen (Term symbol))
sampleCompletion completions
    | count <= 0 = Nothing
    | otherwise =
        Just $
            fromMaybe (error "sampleCompletion: a rank below the count has a completion")
                . unrankCompletion completions
                . Rank
                <$> QC.chooseInteger (0, count - 1)
  where
    Cardinality count = completionCount completions

{- | A generator of the completions, each with a probability in proportion to
its weight, as 'drawCompletion' draws it. 'Nothing' when the completions have
the weight zero. Each choice scales its weights to integers and draws one of
them, so the probabilities are exact.
-}
sampleWeighted :: Completions symbol -> Maybe (QC.Gen (Term symbol))
sampleWeighted = drawCompletion chooseIndex
  where
    chooseIndex weights = do
        let scale = foldr (lcm . denominator) 1 weights
            scaled = [numerator (weight * fromInteger scale) | weight <- weights]
        drawn <- QC.chooseInteger (0, sum scaled - 1)
        pure $ length $ takeWhile (<= drawn) $ scanl1 (+) scaled
