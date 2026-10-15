{- | Compare two generators of one language: they have the same cardinality,
and they give the same value at each checked rank.
-}
module SameRanks (sameRanks) where

import Control.Monad (unless)
import Data.Containers.ListUtils (nubOrd)

import qualified Data.CFTA.Gen.Refinement as LTAGen
import Data.CFTA.Index (Cardinality (..), Rank (..))

{- | Compare two compiled generators. A generator with at most 100000 members
is compared at every rank. A larger one is compared at the first three
ranks, the middle rank, the last two ranks, and 200 ranks from a fixed
sequence.
-}
sameRanks :: (Eq a, Show a) => String -> LTAGen.LTAGen a -> LTAGen.LTAGen a -> IO ()
sameRanks name first second = do
    expected <- either (fail . show) pure $ LTAGen.cardinality first
    actual <- either (fail . show) pure $ LTAGen.cardinality second
    unless (expected == actual)
        $ fail
        $ name <> ": the first generator has " <> show expected <> " members, the second " <> show actual
    let Cardinality total = expected
        ranks
            | total <= 100000 = [0 .. total - 1]
            | otherwise = nubOrd $ [0, 1, 2, total `div` 2, total - 2, total - 1] <> take 200 (iterate next 1)
        next rank = (rank * 6364136223846793005 + 1442695040888963407) `mod` total
        differing = [rank | rank <- ranks, LTAGen.unrank first (Rank rank) /= LTAGen.unrank second (Rank rank)]
    case differing of
        [] -> putStrLn $ name <> ": " <> show total <> " members, the values agree at " <> show (length ranks) <> " ranks"
        rank : _ ->
            fail $
                name
                    <> ": at rank "
                    <> show rank
                    <> " the first generator gives "
                    <> show (LTAGen.unrank first (Rank rank))
                    <> ", the second "
                    <> show (LTAGen.unrank second (Rank rank))
