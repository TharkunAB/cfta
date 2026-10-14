{- | Tests of "Data.CFTA.Gen.Synthesis.Liquid" with Z3, on the data of
"Data.CFTA.Gen.Synthesis.HegelBenchmarks".
-}
module Data.CFTA.Gen.Synthesis.LiquidSpec (spec) where

import Data.List (find)
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldSatisfy)

import Data.CFTA.Formula (Name (..), Sort (..))
import Data.CFTA.Gen.Synthesis.HegelBenchmarks (LiquidBenchmark (..), liquidBenchmarks, listLibrary, measures)
import Data.CFTA.Gen.Synthesis.Liquid (Outcome (..), defaultOptions, renderTerm, synthesize)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Timeout)

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis.Liquid" $
    it "keeps the states of components whose names have an at sign or a backslash" $ do
        benchmark <- maybe (fail "no query RevApp1") pure (find ((== "RevApp1") . liquidName) liquidBenchmarks)
        result <- withZ3Timeout 1000 declarations [] $ \solver ->
            synthesize solver defaultOptions [(rename name, typ) | (name, typ) <- listLibrary] (liquidQuery benchmark)
        fmap (map renderTerm . outcomeSolutions) result `shouldSatisfy` either (const False) ("app\\end (r@v l) l" `elem`)
  where
    rename :: Text -> Text
    rename "rev" = "r@v"
    rename "append" = "app\\end"
    rename name = name
    declarations = [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
