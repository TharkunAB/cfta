{-# LANGUAGE OverloadedStrings #-}

-- | The rule for an abstraction extension, on a toy model of pairs of digits.
module Data.CFTA.Gen.TowerSpec (spec) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA.Formula as F
import Data.CFTA.Gen.Tower (Observation (..), Outcome (..), Result (..), Step (..), Verdict (..))
import qualified Data.CFTA.Gen.Tower as Tower
import Data.CFTA.Refinement.Expression (modulo, refinementFormula, (.==), (.>))
import Data.CFTA.Symbol (Symbol (RefinedSymbol))
import Data.CFTA.Term (Term (Node))

-- | The response of the toy model: is the first digit large, and is the second digit even.
data Response = Response !Bool !Bool
    deriving (Eq, Ord, Show)

spec :: Spec
spec = describe "Data.CFTA.Gen.Tower" $ do
    it "decides predicates of the fragment at a value" $ do
        Tower.evaluate 5 (greaterThan 4) `shouldBe` Just True
        Tower.evaluate 4 (divisibleBy 2) `shouldBe` Just True
        Tower.evaluate 4 (divisibleBy 0) `shouldBe` Nothing
        Tower.evaluate 4 (F.Forall [] F.Top) `shouldBe` Nothing

    it "replaces each exact value by its cube" $ do
        Tower.abstract [] (digit 5) `shouldBe` Just (Node "lit" [])
        Tower.abstract [greaterThan 4] (digit 5) `shouldBe` Just (Node (RefinedSymbol "lit" $ greaterThan 4) [])
        Tower.abstract [greaterThan 4] (digit 3) `shouldBe` Just (Node (RefinedSymbol "lit" $ F.Not $ greaterThan 4) [])

    it "finds the conflicts of a coarse vocabulary" $ do
        map (Set.fromList . map observedResponse . snd) (Tower.conflicts [] observations)
            `shouldBe` [Set.fromList [Response large evenSecond | large <- [False, True], evenSecond <- [False, True]]]
        Tower.conflicts [greaterThan 4, divisibleBy 2] observations `shouldBe` []

    it "tells a wrong spec from a coarse vocabulary" $ do
        Tower.classify (observe 7 2) (observe 9 4) `shouldBe` SpecWrong
        Tower.classify (observe 7 2) (observe 3 2) `shouldBe` TooCoarse

    it "extends the vocabulary twice and then only updates the spec" $ do
        let Result vocabulary final steps outcome = Tower.refine templates fallback [] Map.empty observations
        Set.fromList vocabulary `shouldBe` Set.fromList [greaterThan 4, divisibleBy 2]
        [predicate | Extend predicate <- steps] `shouldBe` vocabulary
        length [() | Update _ _ <- steps] `shouldBe` Map.size final
        agrees vocabulary final `shouldBe` True
        outcome `shouldBe` Agreed

    it "stops with the conflict when no candidate separates it" $ do
        let Result vocabulary _ steps outcome = Tower.refine [] fallback [] Map.empty observations
        vocabulary `shouldBe` []
        [() | Extend _ <- steps] `shouldBe` []
        case outcome of
            Stuck _ tests -> length tests `shouldBe` length observations
            Agreed -> fail "expected a stop"

    it "only updates a spec that is wrong for one term" $ do
        let Result vocabulary final _ _ = Tower.refine templates fallback [] Map.empty observations
            (term, response) = Map.findMin final
            broken = Map.insert term fallback final
            Result vocabulary' repaired steps _ = Tower.refine templates fallback vocabulary broken observations
        steps `shouldBe` [Update term response]
        vocabulary' `shouldBe` vocabulary
        repaired `shouldBe` final
    it "gives a shorter spec than the table of concrete tests" $ do
        let Result vocabulary final _ _ = Tower.refine templates fallback [] Map.empty observations
            concrete =
                Map.fromList
                    [ (observedTest observation, observedResponse observation)
                    | observation <- observations
                    , observedResponse observation /= fallback
                    ]
        Tower.descriptionLength vocabulary final `shouldSatisfy` (< Tower.descriptionLength [] concrete)
    it "adds two predicates together when neither one shortens the spec alone" $ do
        -- A sum is accepted when it is even and every digit is at most 4.
        let accepts term = even (sum values) && all (<= 4) values where values = digitsOf term
            tests =
                [ Observation test (accepts test) | test <- map lit [0 .. 9] <> [Node "add" [lit a, lit b] | a <- [0 .. 9], b <- [0 .. 9]]
                ]
            Result vocabulary final steps outcome = Tower.refine templates False [] Map.empty tests
            concrete = Map.fromList [(observedTest test, True) | test <- tests, observedResponse test]
        outcome `shouldBe` Agreed
        Set.fromList vocabulary `shouldBe` Set.fromList [greaterThan 4, divisibleBy 2]
        take 2 steps `shouldBe` map Extend vocabulary
        Tower.descriptionLength vocabulary final `shouldSatisfy` (< Tower.descriptionLength [] concrete)
  where
    agrees vocabulary final =
        and
            [ Map.findWithDefault fallback term final == observedResponse observation
            | observation <- observations
            , Just term <- [Tower.abstract vocabulary $ observedTest observation]
            ]

-- | The model answers this when the spec has no entry for a term.
fallback :: Response
fallback = Response False False

-- | The model: the response depends on the first digit being above 4, and on the second digit being even.
model :: Integer -> Integer -> Response
model first second = Response (first > 4) (even second)

-- | Every pair of digits, tested once.
observations :: [Observation Response]
observations = [observe first second | first <- [0 .. 9], second <- [0 .. 9]]

-- | The test of one pair, with the response of the model.
observe :: Integer -> Integer -> Observation Response
observe first second = Observation (Node "pair" [digit first, digit second]) (model first second)

-- | A digit leaf as a term.
lit :: Integer -> Term Symbol
lit = digit

-- | The digits of the leaves of a test.
digitsOf :: Term Symbol -> [Integer]
digitsOf (Node symbol []) = [value | value <- [0 .. 9], Node symbol [] == digit value]
digitsOf (Node _ children) = concatMap digitsOf children

-- | A leaf with an exact value.
digit :: Integer -> Term Symbol
digit exact = Node (RefinedSymbol "lit" $ refinementFormula (.== fromInteger exact)) []

-- | The qualifier templates, in the expression syntax of refinements: @v > k@ and @v mod k == 0@.
templates :: [Integer -> F.Formula]
templates = [greaterThan, divisibleBy]

-- | @v > k@.
greaterThan :: Integer -> F.Formula
greaterThan bound = refinementFormula (.> fromInteger bound)

-- | @v mod k == 0@.
divisibleBy :: Integer -> F.Formula
divisibleBy divisor = refinementFormula $ \v -> modulo v (fromInteger divisor) .== 0
