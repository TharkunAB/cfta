-- Check the source midpoint arithmetic without allocating a large array.
import Control.Monad (unless)

-- | Preserve the historical overflow and check the repaired source expression.
main :: IO ()
main = do
    let high = maxBound - 1 :: Int
        low = high `quot` 2 + 1
        historical = (low + high) `quot` 2
        repaired = low + (high - low) `quot` 2
        expected = (toInteger low + toInteger high) `quot` 2
    print (historical, repaired, expected)
    unless (historical < 0 && toInteger repaired == expected && low <= repaired && repaired <= high) $
        fail "weighted midpoint arithmetic changed"
