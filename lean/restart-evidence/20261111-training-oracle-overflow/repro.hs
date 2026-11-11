import qualified Data.CFTA as F
import Data.CFTA.Index (Size (..))
import qualified Data.CFTA.Sized.Prefix as Prefix
import qualified Data.CFTA.Sized.Prefix.Train as Train
import qualified Data.CFTA.Term as T
import qualified Data.Map.Strict as Map

main :: IO ()
main = do
    let automaton = F.fromTerms [T.Node "a" [T.Node "a" []]]
        weights = Map.singleton "a" 400
        oracle = Train.automatonOracle automaton 2
    case Prefix.prefixCompletions (Size 2) automaton of
        Left problem -> fail (show problem)
        Right completions -> do
            putStrLn $ "completion_log_partition = " ++ show (Train.logPartition weights completions)
            putStrLn $ "automaton_log_partition = " ++ show (Train.oracleLogPartition oracle weights)
            putStrLn $ "completion_expectations = " ++ show (Train.oracleExpectations (Train.completionsOracle completions) weights)
            putStrLn $ "automaton_expectations = " ++ show (Train.oracleExpectations oracle weights)
