import Control.Monad (forM_, unless)
import qualified Data.CFTA as F
import Data.CFTA.Index (Size (..))
import qualified Data.CFTA.Sized.Prefix as Prefix
import qualified Data.CFTA.Sized.Prefix.Train as Train
import qualified Data.CFTA.Term as T
import qualified Data.Map.Strict as Map
import Text.Printf (printf)

main :: IO ()
main = do
    let automaton = F.fromTerms [T.Node "a" [T.Node "a" []]]
    case Prefix.prefixCompletions (Size 2) automaton of
        Left problem -> fail (show problem)
        Right completions -> forM_ [400, -400] $ \weight -> do
            let weights = Map.singleton "a" weight
                expected = 2 * weight
            unless (near expected $ Train.logPartition weights completions) $
                fail "The completion log-partition changed."
            (completionTotal, completionCount) <- verify (Train.completionsOracle completions) weights expected
            (groupedTotal, groupedCount) <- verify (Train.automatonOracle automaton 2) weights expected
            printf
                "weight=%.0f completion=(%.0f,%.0f) grouped=(%.0f,%.0f)\n"
                weight
                completionTotal
                completionCount
                groupedTotal
                groupedCount

-- | Check each partition and normalized expected count before reporting rounded values.
verify :: Train.Oracle String -> Train.LogWeights String -> Double -> IO (Double, Double)
verify oracle weights expected = do
    let (total, counts) = Train.oracleExpectations oracle weights
        count = Map.findWithDefault (0 / 0) "a" counts
    unless
        ( near expected (Train.oracleLogPartition oracle weights)
            && near expected total
            && Map.keys counts == ["a"]
            && near 2 count
        )
        $ fail
        $ show (weights, total, counts)
    pure (total, count)

-- | Compare finite numbers at the regression tolerance.
near :: Double -> Double -> Bool
near expected found = not (isNaN found || isInfinite found) && abs (expected - found) < 1e-9
