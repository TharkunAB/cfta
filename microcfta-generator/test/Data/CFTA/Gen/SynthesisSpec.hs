{- | Tests of the syntax of "Data.CFTA.Gen.Synthesis" and
"Data.CFTA.Gen.Synthesis.Liquid" on the data of
"Data.CFTA.Gen.Synthesis.HooglePlus" and "Data.CFTA.Gen.Synthesis.HegelBenchmarks".
-}
module Data.CFTA.Gen.SynthesisSpec (spec) where

import Data.Maybe (mapMaybe)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Gen.Synthesis
import Data.CFTA.Gen.Synthesis.HegelBenchmarks
import Data.CFTA.Gen.Synthesis.HooglePlus
import Data.CFTA.Gen.Synthesis.Liquid (LiquidQuery (..), parseRType, renderRType)

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis" $ do
    it "parses the Hoogle+ data, and the printers give each type and program back" $ do
        let benchmarks = hooglePlusBenchmarks <> stackOverflowBenchmarks
            types =
                map snd (hooglePlusComponents <> augmentedComponents)
                    <> concat [queryGoal query : map snd (queryArguments query) | query <- map benchmarkQuery benchmarks]
            programs = mapMaybe benchmarkSolution benchmarks
        [typ | typ <- types, parseType (Text.pack (renderType typ)) /= Right typ] `shouldBe` []
        [solution | solution <- programs, parseProgram (Text.pack (renderProgram solution)) /= Right solution] `shouldBe` []
    it "parses the Hegel data, and the printer gives each refinement type back" $ do
        let libraries = [listLibrary, pairLibrary, booleanLibrary, lookupLibrary, arrayLibrary, stringLibrary, functionLibrary]
            types =
                map snd (concat libraries)
                    <> concat [liquidGoal query : map snd (liquidArguments query) | query <- map liquidQuery liquidBenchmarks]
        [typ | typ <- types, parseRType (Text.pack (renderRType typ)) /= Right typ] `shouldBe` []
