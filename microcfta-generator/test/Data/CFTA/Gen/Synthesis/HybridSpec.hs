{- | An end-to-end test of "Data.CFTA.Gen.Synthesis.Hybrid" on four small
queries of "Data.CFTA.Gen.Synthesis.HegelBenchmarks": the hybrid finds
Hegel's solution of each one, and the abstracting checker accepts it.
-}
module Data.CFTA.Gen.Synthesis.HybridSpec (spec) where

import Control.Monad (forM)
import Data.List (find)
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Formula (Name (..), Sort (..))
import Data.CFTA.Gen.Synthesis (renderProgram)
import Data.CFTA.Gen.Synthesis.HegelBenchmarks (LiquidBenchmark (..), liquidBenchmarks, measures)
import Data.CFTA.Gen.Synthesis.Hybrid (HybridOutcome (..), defaultHybridOptions, synthesizeHybrid)
import Data.CFTA.Gen.Synthesis.Liquid (Checker (..), checker)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Timeout)

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis.Hybrid" $
    it "solves four of Hegel's queries, and the abstracting checker accepts each solution" $ do
        results <- withZ3Timeout 1000 declarations [] $ \solver ->
            forM cases $ \(name, _) -> do
                benchmark <- maybe (fail ("no query " <> show name)) pure (find ((== name) . liquidName) liquidBenchmarks)
                outcome <- synthesizeHybrid solver defaultHybridOptions (liquidLibrary benchmark) (liquidQuery benchmark)
                accepted <- case hybridSolution outcome of
                    Nothing -> pure False
                    Just program -> do
                        check <- checker solver (liquidLibrary benchmark) (liquidQuery benchmark)
                        checkProgram check program
                pure (name, renderProgram <$> hybridSolution outcome, accepted)
        results `shouldBe` [(name, Just solution, True) | (name, solution) <- cases]
  where
    cases :: [(Text, String)]
    cases =
        [ ("RevApp1", "append (rev l) l")
        , ("Nth_Incr1", "nth l (incr n)")
        , ("RevZip1", "zip (rev f) s")
        , ("MapDouble1", "map g (map f l)")
        ]
    declarations = [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
