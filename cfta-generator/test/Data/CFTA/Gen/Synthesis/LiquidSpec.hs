{- | Tests of "Data.CFTA.Gen.Synthesis.Liquid" with Z3, on the data of
"Data.CFTA.Gen.Synthesis.HegelBenchmarks".
-}
module Data.CFTA.Gen.Synthesis.LiquidSpec (spec) where

import Data.List (find)
import Data.Text (Text)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Formula (Name (..), Sort (..))
import qualified Data.CFTA.Gen.Synthesis as Synthesis
import Data.CFTA.Gen.Synthesis.HegelBenchmarks (LiquidBenchmark (..), liquidBenchmarks, listLibrary, measures)
import Data.CFTA.Gen.Synthesis.Liquid ((-->), (.:))
import qualified Data.CFTA.Gen.Synthesis.Liquid as Liquid
import Data.CFTA.Refinement.Expression (variable, (.==), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Timeout)

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis.Liquid" $ do
    it "keeps the states of components whose names have an at sign or a backslash" $ do
        benchmark <- maybe (fail "no query RevApp1") pure (find ((== "RevApp1") . liquidName) liquidBenchmarks)
        result <- withZ3Timeout 1000 declarations [] $ \solver ->
            Liquid.synthesize solver Liquid.defaultOptions [(rename name, typ) | (name, typ) <- listLibrary] (liquidQuery benchmark)
        fmap (map Liquid.renderTerm . Liquid.outcomeSolutions) result
            `shouldSatisfy` either (const False) ("app\\end (r@v l) l" `elem`)

    it "checks a callback's result over the required domain" $
        withZ3Timeout 1000 [(Name "ap", FunctionSort [IntSort, IntSort] IntSort)] [] $ \solver -> do
            let int = Synthesis.TCons "Int" []
                integer = Liquid.plain int
                exactly n = Liquid.refined int (.== n)
                callback input result = ("x" .: input) --> result
                goal = exactly 0
                -- The supplied function must work at zero. It may accept more inputs.
                callAtZero = ("f" .: callback (exactly 0) goal) --> goal
                zero = callback integer goal
                one = callback integer (exactly 1)
                positiveOnly = callback (Liquid.refined int (.>= 1)) goal
                query = Liquid.LiquidQuery [] goal
                options = Liquid.defaultOptions{Liquid.optionMaximumSize = 1}
                cases = [("one", one, False), ("positiveOnly", positiveOnly, False), ("zero", zero, True)]
                verify (name, typ, valid) = do
                    let library = [("callAtZero", callAtZero), (name, typ)]
                        program = Synthesis.App (Synthesis.Var "callAtZero") (Synthesis.Var name)
                    result <- Liquid.synthesize solver options library query
                    fmap (map Liquid.renderTerm . Liquid.outcomeSolutions) result
                        `shouldBe` Right ["callAtZero " <> Text.unpack name | valid]
                    checker <- Liquid.checker solver library query
                    Liquid.checkProgram checker program >>= (`shouldBe` valid)
                    precise <- Liquid.preciseChecker solver library query
                    Liquid.checkProgram precise program >>= (`shouldBe` valid)
            mapM_ verify cases

    it "uses an earlier argument in a callback's contract" $
        withZ3Timeout 1000 [(Name "ap", FunctionSort [IntSort, IntSort] IntSort)] [] $ \solver -> do
            let int = Synthesis.TCons "Int" []
                integer = Liquid.plain int
                goal = Liquid.refined int (.== 7)
                -- A function that accepts every integer and returns its input.
                identity = ("x" .: integer) --> Liquid.refined int (.== variable "x")
                zero = ("x" .: integer) --> Liquid.refined int (.== 0)
                -- The callback must return n when applied to n.
                callback = ("x" .: Liquid.refined int (.== variable "n")) --> Liquid.refined int (.== variable "n")
                call = ("n" .: integer) --> ("f" .: callback) --> Liquid.refined int (.== variable "n")
                library = [("call", call), ("identity", identity), ("zero", zero), ("seven", goal)]
                program name = Synthesis.App (Synthesis.App (Synthesis.Var "call") (Synthesis.Var "seven")) (Synthesis.Var name)
            checker <- Liquid.preciseChecker solver library (Liquid.LiquidQuery [] goal)
            Liquid.checkProgram checker (program "identity") >>= (`shouldBe` True)
            Liquid.checkProgram checker (program "zero") >>= (`shouldBe` False)
  where
    rename :: Text -> Text
    rename "rev" = "r@v"
    rename "append" = "app\\end"
    rename name = name
    declarations = [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
