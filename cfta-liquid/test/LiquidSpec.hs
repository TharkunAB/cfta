{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{- | Tests of "Data.CFTA.Liquid": the generators of SortedLists, SafeDivision,
and LiquidPairs from Liquid Haskell specifications have the cardinality and
the ranks of the hand-written generators of the examples, and the
translation rejects the specifications that it cannot translate exactly.
-}
module Main (main) where

-- A measure names each child, as in \element _ -> element, as a contract does.
{- HLINT ignore "Use const" -}
-- The specification of Division declares data, so the Haskell type is data too.
{- HLINT ignore "Use newtype instead of data" -}

import Control.Monad (forM_)
import Data.Containers.ListUtils (nubOrd)
import GHC.Generics (Generic)
import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, hspec, it, shouldBe)

import Data.CFTA.Gen.Refinement.Derive (atom)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Index (Cardinality (..), Rank (..))
import Data.CFTA.Liquid (LiquidError (..), Specifications, deriveLTAFromLiquid, liquidAnnotations, specifications)
import Data.CFTA.Liquid.TH (liquidSpecifications)
import Data.CFTA.Refinement.Expression (Refinement, (.&&), (./=), (.<), (.<=), (.==))

-- | The Liquid Haskell specifications of this module.
specs :: Specifications
specs = $(liquidSpecifications)

-- * Sorted lists

{-@ measure hd :: IncList -> Integer
        hd Emp = 1000001
        hd (Cons x xs) = x
  @-}

{-@ data IncList = Emp
                 | Cons { x :: {v:Integer | 0 <= v && v <= 1000000}, xs :: {v:IncList | x <= hd v} }
  @-}

-- | A list that the specifications above keep sorted.
data IncList = Emp | Cons Integer IncList
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The elements of a list.
toList :: IncList -> [Integer]
toList Emp = []
toList (Cons element rest) = element : toList rest

-- | The derived sorted lists.
derivedSortedLists :: Either LiquidError (LTAGen.LTAGen [Integer])
derivedSortedLists = fmap toList <$> deriveLTAFromLiquid @IncList 8 (atom @Integer LTAGen.every) specs

-- | The hand-written sorted lists of SortedLists.hs.
sortedLists :: LTAGen.LTAGen [Integer]
sortedLists = LTAGen.recurUpTo 8 $ \rest -> LTAGen.oneof [nil, cons rest]
  where
    nil = LTAGen.leaf [] "nil" (.== 1000001)
    cons rest =
        LTAGen.measured
            "cons"
            (\element restHead -> element .<= restHead)
            (\element _ -> element)
            $ LTAGen.do
                element <- LTAGen.every `LTAGen.satisfying` (\v -> 0 .<= v .&& v .<= 1000000)
                elements <- rest
                LTAGen.pure (element : elements)

-- * Safe division

{-@ type Denominator = {v:Integer | 0 <= v && v <= 5 && v /= 0} @-}

{-@ data Division = Divide { d :: Denominator } @-}

-- | A division of twelve by a denominator.
data Division = Divide Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The derived divisions.
derivedDivisions :: Either LiquidError (LTAGen.LTAGen (Integer, Integer))
derivedDivisions =
    fmap (\(Divide denominator) -> (denominator, 12 `div` denominator))
        <$> deriveLTAFromLiquid @Division 0 (atom @Integer LTAGen.every) specs

-- | The hand-written divisions of SafeDivision.hs.
divisions :: LTAGen.LTAGen (Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    denominator <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (denominator, 12 `div` denominator)

-- * Liquid pairs

{-@ data Pair = Pair { left :: Integer, right :: {v:Integer | left < v} } @-}

-- | A pair of two values.
data Pair = Pair Integer Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Values that the solver knows only by the range that contains them.
ranged :: [(Integer, Refinement)]
ranged =
    [ (1, \v -> 0 .<= v .&& v .< 2)
    , (3, \v -> 2 .<= v .&& v .< 4)
    , (5, \v -> 4 .<= v .&& v .< 6)
    ]

-- | The derived pairs. The values come from the ranged pool.
derivedPairs :: Either LiquidError (LTAGen.LTAGen (Integer, Integer))
derivedPairs =
    fmap (\(Pair leftValue rightValue) -> (leftValue, rightValue))
        <$> deriveLTAFromLiquid @Pair 0 (atom @Integer (LTAGen.pool ranged)) specs

-- | The hand-written pairs of LiquidPairs.hs.
pairs :: LTAGen.LTAGen (Integer, Integer)
pairs = LTAGen.guarded "pair" (\leftValue rightValue -> leftValue .< rightValue) $ LTAGen.do
    leftValue <- LTAGen.pool ranged
    rightValue <- LTAGen.pool ranged
    LTAGen.pure (leftValue, rightValue)

{- | Compile both generators, and expect the same cardinality and the same
value at each checked rank: every rank of a small generator, and the first
three, the middle, the last two, and 200 ranks of a fixed sequence of a large
one.
-}
sameRanks :: (Eq a, Show a) => LTAGen.LTAGen a -> Either LiquidError (LTAGen.LTAGen a) -> Expectation
sameRanks handWritten derived = case derived of
    Left err -> expectationFailure $ show err
    Right generator -> do
        expected <- LTAGen.compile handWritten
        actual <- LTAGen.compile generator
        LTAGen.cardinality actual `shouldBe` LTAGen.cardinality expected
        case LTAGen.cardinality expected of
            Left err -> expectationFailure $ show err
            Right (Cardinality total) -> do
                let next rank = (rank * 6364136223846793005 + 1442695040888963407) `mod` total
                    checked
                        | total <= 100000 = [0 .. total - 1]
                        | otherwise = nubOrd $ [0, 1, 2, total `div` 2, total - 2, total - 1] <> take 200 (iterate next 1)
                forM_ checked $ \rank -> LTAGen.unrank actual (Rank rank) `shouldBe` LTAGen.unrank expected (Rank rank)

spec :: Spec
spec = describe "Data.CFTA.Liquid" $ do
    it "derives SortedLists from a data specification and a measure" $
        sameRanks sortedLists derivedSortedLists
    it "derives SafeDivision from a data specification with a refinement alias" $
        sameRanks divisions derivedDivisions
    it "derives LiquidPairs from a data specification that relates two fields" $
        sameRanks pairs derivedPairs
    it "rejects a second measure of the datatype" $
        liquidAnnotations @IncList (rejected [hd, len, incList "x <= hd v"])
            `shouldBeError` Untranslatable "IncList" "the measures hd, len are more than one: a node of a liquid tree automaton has one integer"
    it "rejects a product of two terms that are not constants" $
        liquidAnnotations @IncList (rejected [hd, incList "x * hd v <= 10"])
            `shouldBeError` Untranslatable "field xs of Cons" "a product of two terms that are not constants is not linear"
    it "rejects a name that is not a field" $
        liquidAnnotations @IncList (rejected [hd, incList "y <= hd v"])
            `shouldBeError` Untranslatable "field xs of Cons" "y is not a field"
    it "rejects a measure without an equation for a constructor" $
        liquidAnnotations @IncList
            (rejected ["measure hd :: IncList -> Integer\n        hd (Cons x xs) = x", incList "x <= hd v"])
            `shouldBeError` Untranslatable "the measure hd of Emp" "the measure has no equation for this constructor"
    it "reports a datatype without a data specification" $
        liquidAnnotations @IncList (rejected [hd]) `shouldBeError` NoDataSpecification "IncList"
  where
    shouldBeError result expected = either Just (const Nothing) result `shouldBe` Just expected
    rejected texts = specifications [("Rejected.hs", line, 4, text) | (line, text) <- zip [1 ..] texts]
    hd = "measure hd :: IncList -> Integer\n        hd Emp = 1000001\n        hd (Cons x xs) = x"
    len = "measure len :: IncList -> Integer\n        len Emp = 0\n        len (Cons x xs) = 1 + len xs"
    incList refinement = "data IncList = Emp | Cons { x :: Integer, xs :: {v:IncList | " <> refinement <> "} }"

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec spec
