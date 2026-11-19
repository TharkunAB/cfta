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

    it "requires callback domain coverage even with an unrefined result" $
        withZ3Timeout 1000 [(Name "ap", FunctionSort [IntSort, IntSort] IntSort)] [] $ \solver -> do
            let int = Synthesis.TCons "Int" []
                integer = Liquid.plain int
                required = ("arg" .: Liquid.refined int (.== 0)) --> integer
                narrow = ("x" .: Liquid.refined int (.>= 1)) --> integer
                wide = ("x" .: integer) --> integer
                consumer = ("callback" .: required) --> integer
                query = Liquid.LiquidQuery [] integer
                options = Liquid.defaultOptions{Liquid.optionMaximumSize = 1}
                verify (typ, valid) = do
                    let library = [("callAtZero", consumer), ("supplied", typ)]
                        program = Synthesis.App (Synthesis.Var "callAtZero") (Synthesis.Var "supplied")
                    result <- Liquid.synthesize solver options library query
                    fmap (map Liquid.renderTerm . Liquid.outcomeSolutions) result
                        `shouldBe` Right ["callAtZero supplied" | valid]
                    abstracted <- Liquid.checker solver library query
                    precise <- Liquid.preciseChecker solver library query
                    Liquid.checkProgram abstracted program >>= (`shouldBe` valid)
                    Liquid.checkProgram precise program >>= (`shouldBe` valid)
            mapM_ verify [(narrow, False), (wide, True)]

    it "checks nested arrow binders with lexical scope" $
        withZ3Timeout 1000 [(Name "ap", FunctionSort [IntSort, IntSort] IntSort)] [] $ \solver -> do
            let parse = either fail pure . Liquid.parseRType
            supplied <- parse "x:{v:Int | v == 7} -> x:{v:Int | v == x + 1} -> {v:Int | v == x}"
            good <- parse "f:(a:{v:Int | v == 7} -> b:{v:Int | v == 8} -> {v:Int | v == 8}) -> Int"
            bad <- parse "f:(a:{v:Int | v == 7} -> b:{v:Int | v == 9} -> {v:Int | v == 9}) -> Int"
            ordinary <- parse "f:(Int -> Int) -> Int"
            let int = Synthesis.TCons "Int" []
                query =
                    Liquid.LiquidQuery
                        [("callback", supplied), ("restricted", ("x" .: Liquid.refined int (.== 7)) --> Liquid.plain int)]
                        (Liquid.plain int)
                library = [("valid", good), ("invalid", bad), ("ordinary", ordinary), ("curried", supplied)]
                program headName argument = Synthesis.App (Synthesis.Var headName) (Synthesis.Var argument)
            Liquid.parseRType (Text.pack (Liquid.renderRType good)) `shouldBe` Right good
            checker <- Liquid.preciseChecker solver library query
            Liquid.checkProgram checker (program "valid" "callback") >>= (`shouldBe` True)
            Liquid.checkProgram checker (program "valid" "curried") >>= (`shouldBe` True)
            Liquid.checkProgram checker (program "invalid" "callback") >>= (`shouldBe` False)
            Liquid.checkProgram checker (program "ordinary" "restricted") >>= (`shouldBe` False)

    it "renders the refinement value separately from an arrow or quantifier binding" $ do
        let roundtrip source = do
                typ <- either fail pure $ Liquid.parseRType source
                Liquid.parseRType (Text.pack (Liquid.renderRType typ)) `shouldBe` Right typ
        mapM_ roundtrip ["x:Int -> {r:Int | forall v. r = x + v}", "v:Int -> {r:Int | r = v}"]

    it "retains callback contracts after a reduction round" $
        withZ3Timeout 1000 [(Name "ap", FunctionSort [IntSort, IntSort] IntSort)] [] $ \solver -> do
            let int = Synthesis.TCons "Int" []
                integer = Liquid.plain int
                unit = Liquid.plain (Synthesis.TCons "Unit" [])
                exactly n = Liquid.refined int (.== n)
                required = ("arg" .: Liquid.refined int (.== variable "n")) --> integer
                consumer = ("n" .: integer) --> ("f" .: required) --> exactly 9
                callback n = ("x" .: exactly n) --> integer
                library =
                    [ ("consume", consumer)
                    , ("seven", ("u" .: unit) --> exactly 7)
                    , ("unit", unit)
                    , ("good", callback 7)
                    , ("bad", callback 8)
                    ]
                query = Liquid.LiquidQuery [] (exactly 9)
                options = Liquid.defaultOptions{Liquid.optionMaximumSize = 2}
            result <- Liquid.synthesize solver options library query
            fmap (map Liquid.renderTerm . Liquid.outcomeSolutions) result
                `shouldBe` Right ["consume (seven unit) good"]

    it "checks the declared domain of a function-valued solution" $
        withZ3Timeout 1000 [(Name "ap", FunctionSort [IntSort, IntSort] IntSort)] [] $ \solver -> do
            let int = Synthesis.TCons "Int" []
                integer = Liquid.plain int
                narrow = ("x" .: Liquid.refined int (.== 7)) --> integer
                wide = ("x" .: integer) --> integer
                goal = Liquid.plain (Synthesis.TFun int int)
                query = Liquid.LiquidQuery [("narrow", narrow), ("wide", wide)] goal
                options = Liquid.defaultOptions{Liquid.optionMaximumSize = 1}
            result <- Liquid.synthesize solver options [] query
            fmap (map Liquid.renderTerm . Liquid.outcomeSolutions) result `shouldBe` Right ["wide"]
            checker <- Liquid.preciseChecker solver [] query
            Liquid.checkProgram checker (Synthesis.Var "narrow") >>= (`shouldBe` False)
            Liquid.checkProgram checker (Synthesis.Var "wide") >>= (`shouldBe` True)
  where
    rename :: Text -> Text
    rename "rev" = "r@v"
    rename "append" = "app\\end"
    rename name = name
    declarations = [(Name measureName, FunctionSort (replicate arity IntSort) IntSort) | (measureName, arity) <- measures]
