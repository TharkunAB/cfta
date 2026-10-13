-- These callbacks violate the documented WeightedIndexed obligations.
-- Numeric metadata checks cannot establish callback validity or coverage.
import qualified Data.CFTA.Ranked.Internal as Ranked
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))

-- | Show an out-of-range sampled rank and a valid rank with no sampling ticket.
main :: IO ()
main = do
    let make callback = Ranked.fromWeightedIndexedOnDemand $ Ranked.WeightedIndexed 2 2 id callback
    case make (const 2) of
        Left err -> print err
        Right source -> do
            print $ runExact $ Ranked.lowerWithRank source
            print $ Ranked.unrank source 2
    case make (const 0) of
        Left err -> print err
        Right source -> do
            print $ runExact $ Ranked.lowerWithRank source
            print $ Ranked.unrank source 1
