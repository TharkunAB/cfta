{- | Tests of the syntax of "Data.CFTA.Gen.Synthesis" on the Hoogle+ data of
"Data.CFTA.Gen.Synthesis.HooglePlus".
-}
module Data.CFTA.Gen.SynthesisSpec (spec) where

import Data.Maybe (mapMaybe)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Gen.Synthesis
import Data.CFTA.Gen.Synthesis.HooglePlus

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis" $
    it "parses the Hoogle+ data, and the printers give each type and program back" $ do
        let benchmarks = hooglePlusBenchmarks <> stackOverflowBenchmarks
            types =
                map snd (hooglePlusComponents <> augmentedComponents)
                    <> concat [queryGoal query : map snd (queryArguments query) | query <- map benchmarkQuery benchmarks]
            programs = mapMaybe benchmarkSolution benchmarks
        [typ | typ <- types, parseType (Text.pack (renderType typ)) /= Right typ] `shouldBe` []
        [solution | solution <- programs, parseProgram (Text.pack (renderProgram solution)) /= Right solution] `shouldBe` []
