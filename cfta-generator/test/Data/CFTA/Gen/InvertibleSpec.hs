-- | Spike: generators built from invertible blocks rank their values.
module Data.CFTA.Gen.InvertibleSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Gen (Gen)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import Data.CFTA.Ranked.Internal (Indexed (..))
import Data.CFTA.Term (Term (Node))

leaves :: Integer -> Gen String (Term String)
leaves count =
    Gen.invertible
        (Indexed (Cardinality count) (\(Rank r) -> Node ('#' : show r) []))
        ( \term -> case term of
            Node ('#' : digits) [] | [(n, "")] <- reads digits, n >= 0, n < count -> Just (Rank n)
            _ -> Nothing
        )

operation :: String -> Gen String (Term String) -> Gen String (Term String)
operation name child =
    Gen.node name $
        Gen.invertibleMap
            (\(left, right) -> Node name [left, right])
            ( \term -> case term of
                Node found [left, right] | found == name -> Just (left, right)
                _ -> Nothing
            )
            (Gen.invertiblePair child child)

step :: Gen String (Term String) -> Gen String (Term String)
step child = Gen.oneof [child, operation "add" child, operation "mul" child]

spec :: Spec
spec = describe "invertible blocks" $ do
    it "rank every value of a small generator back" $ do
        let generator = step (step (leaves 3))
            total = either (const 0) (\(Cardinality n) -> n) (Gen.cardinality generator)
        total `shouldBe` 903
        -- A choice counts a member of two alternatives twice, so a value can have several ranks.
        mapM_
            ( \rank -> do
                let value = Gen.unrank generator rank
                ranks <- either (fail . show) pure (value >>= Gen.rankOfInvertible generator)
                ranks `shouldSatisfy` elem rank
                map (Gen.unrank generator) ranks `shouldBe` map (const value) ranks
            )
            (everyRank (Cardinality total))
    it "rank a value at a late rank without listing a million leaves" $ do
        let generator = step (leaves 1000000)
            ranks =
                map
                    Rank
                    [0, 999999, 1000000, 1000000 + 10 ^ (12 :: Int) - 1, 1000000 + 10 ^ (12 :: Int), 1000000 + 2 * 10 ^ (12 :: Int) - 1]
        mapM_
            (\rank -> (Gen.unrank generator rank >>= Gen.rankOfInvertible generator) `shouldBe` Right [rank])
            ranks
    it "keep the inverse through pay and atomic" $ do
        let generators = [Gen.pay (step (leaves 3)), Gen.atomic (step (leaves 3))]
        mapM_
            ( \generator ->
                mapM_
                    (\rank -> (Gen.unrank generator rank >>= Gen.rankOfInvertible generator) `shouldBe` Right [rank])
                    (everyRank (Cardinality 21))
            )
            generators
    it "has no rank for a value of a map without an inverse" $
        Gen.rankOfInvertible (Node "x" [] <$ leaves 2) (Node "x" []) `shouldSatisfy` either (const True) (const False)
    it "has no rank for a value that the generator does not hold" $
        Gen.rankOfInvertible (step (leaves 3)) (Node "#9" []) `shouldBe` Right []
