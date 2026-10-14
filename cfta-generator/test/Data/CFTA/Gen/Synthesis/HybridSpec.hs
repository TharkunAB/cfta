{- | An end-to-end test of "Data.CFTA.Gen.Synthesis.Hybrid" on four small
queries of "Data.CFTA.Gen.Synthesis.HegelBenchmarks": the hybrid finds
Hegel's solution of each one, and the abstracting checker accepts it. A
second test runs Hegel through the fallback.
-}
module Data.CFTA.Gen.Synthesis.HybridSpec (spec) where

import Control.Monad (forM)
import Data.List (find)
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Formula (Name (..), Sort (..))
import Data.CFTA.Gen.Synthesis (renderProgram)
import Data.CFTA.Gen.Synthesis.HegelBenchmarks (LiquidBenchmark (..), liquidBenchmarks, measures)
import Data.CFTA.Gen.Synthesis.Hybrid (HybridOptions (..), HybridOutcome (..), defaultHybridOptions, synthesizeHybrid)
import Data.CFTA.Gen.Synthesis.Liquid (Checker (..), Outcome (..), checker, defaultOptions, renderTerm)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Timeout)

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis.Hybrid" $ do
    it "solves four of Hegel's queries, and the abstracting checker accepts each solution" $ do
        results <- withZ3Timeout 1000 declarations [] $ \solver ->
            forM cases $ \(name, _) -> do
                benchmark <- benchmarkNamed name
                -- Without the fallback, so that a slow machine cannot give Hegel's answer.
                outcome <- synthesizeHybrid solver hybridOnly (liquidLibrary benchmark) (liquidQuery benchmark)
                accepted <- case hybridSolution outcome of
                    Nothing -> pure False
                    Just program -> do
                        check <- checker solver (liquidLibrary benchmark) (liquidQuery benchmark)
                        checkProgram check program
                pure (name, renderProgram <$> hybridSolution outcome, accepted)
        results `shouldBe` [(name, Just solution, True) | (name, solution) <- cases]
    it "runs Hegel when the hybrid has no program" $ do
        -- At size 1 the hybrid finds no program at once, so the time budget plays no part.
        benchmark <- benchmarkNamed "RevApp1"
        outcome <-
            withZ3Timeout 1000 declarations [] $ \solver ->
                synthesizeHybrid
                    solver
                    defaultHybridOptions{hybridMaximumSize = 1, hybridFallback = Just (60, defaultOptions)}
                    (liquidLibrary benchmark)
                    (liquidQuery benchmark)
        hybridSolution outcome `shouldBe` Nothing
        fmap (map renderTerm . outcomeSolutions) <$> hybridFallbackOutcome outcome `shouldBe` Just (Right ["append (rev l) l"])
  where
    hybridOnly = defaultHybridOptions{hybridFallback = Nothing}
    benchmarkNamed name = maybe (fail ("no query " <> show name)) pure (find ((== name) . liquidName) liquidBenchmarks)
    cases :: [(Text, String)]
    cases =
        [ ("RevApp1", "append (rev l) l")
        , ("Nth_Incr1", "nth l (incr n)")
        , ("RevZip1", "zip (rev f) s")
        , ("MapDouble1", "map g (map f l)")
        ]
    declarations = [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
