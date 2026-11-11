-- | QuickCheck generators of the completions of a prefix.
module Data.CFTA.Sized.Prefix.QuickCheck (
    sampleCompletion,
    sampleWeighted,
) where

import Data.Maybe (fromMaybe)
import qualified Test.QuickCheck as QC

import Data.CFTA.Index (Cardinality (..), Rank (..))
import Data.CFTA.Ranked.QuickCheck (QuickCheckBackend (..))
import Data.CFTA.Sized.Prefix (Completions, completionCount, lowerCompletions, unrankCompletion)
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
its weight: the sampler of 'lowerCompletions' for QuickCheck. 'Nothing' when
the completions have the weight zero. The weights become integers, so the
probabilities are exact.
-}
sampleWeighted :: Completions symbol -> Maybe (QC.Gen (Term symbol))
sampleWeighted completions = generator <$> lowerCompletions completions
  where
    generator (QuickCheckBackend generated) = generated
