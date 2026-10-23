{- | An automaton import whose leaf symbol stands for an integer interval:
counts against a closed formula, rank round trips, and the ranks of the
listed route.
-}
module Data.CFTA.Gen.IndexedLeafSpec (spec) where

import qualified Data.Map.Strict as Map
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Gen (Gen, LeafSource (..))
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.ManySorted
import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Term (Term (Node))

data Sort = Int | Bool
    deriving (Eq, Ord, Show)

-- | The leaf symbol of the sort Int.
leafSymbol :: String
leafSymbol = "<Int>"

value :: Integer -> String
value n = '#' : show n

-- | Int has a leaf symbol, add, and ite. Bool has lt.
signature :: [SortedFunction Sort String] -> SortedSignature Sort String
signature leaves =
    SortedSignature
        { sortedSorts = [Int, Bool]
        , sortedFunctions =
            leaves
                <> [ SortedFunction "add" [Int, Int] Int
                   , SortedFunction "lt" [Int, Int] Bool
                   , SortedFunction "ite" [Bool, Int, Int] Int
                   ]
        , sortedRoots = [Int, Bool]
        , sortedValues = []
        }

-- | The interval 0..high as a leaf source.
interval :: Integer -> LeafSource String
interval high =
    LeafSource
        { leafCount = Cardinality (high + 1)
        , leafTerm = \(Rank r) -> Node (value r) []
        , leafRank = \term -> case term of
            Node ('#' : digits) [] | [(n, "")] <- reads digits, n >= 0, n <= high -> Just (Rank n)
            _ -> Nothing
        }

indexed :: Integer -> Gen String (Term String)
indexed high = case signatureAutomaton (signature [SortedFunction leafSymbol [] Int]) of
    Left err -> error (show err)
    Right automaton ->
        Gen.fromAutomatonWithLeaves (Map.singleton leafSymbol (interval high)) $
            Interned.fromRows (FTA.initialState automaton) (FTA.transitionTable automaton)

listed :: Integer -> Gen String (Term String)
listed high = either (error . show) id $ signatureGen $ signature [SortedFunction (value n) [] Int | n <- [0 .. high]]

-- | The number of terms of each size, from the recurrences of the signature.
formula :: Integer -> [Integer]
formula values = take 12 [intTable !! s + boolTable !! s | s <- [1 ..]]
  where
    intTable, boolTable :: [Integer]
    intTable = 0 : [ints s | s <- [1 ..]]
    boolTable = 0 : [bools s | s <- [1 ..]]
    ints s = (if s == 1 then values else 0) + pairs s + triples s
    bools = pairs
    pairs s = sum [intTable !! a * intTable !! b | a <- [1 .. s - 2], let b = s - 1 - a, b >= 1]
    triples s =
        sum
            [ boolTable !! c * intTable !! a * intTable !! b | c <- [1 .. s - 3], a <- [1 .. s - 2 - c], let b = s - 1 - c - a, b >= 1
            ]

spec :: Spec
spec = describe "Gen.fromAutomatonWithLeaves" $ do
    it "counts a million values as the closed formula, without listing them" $ do
        let generator = Gen.upToSize 9 (indexed 999999)
        [Gen.countAtSize generator s | s <- [1 .. 9]] `shouldBe` map (Right . Cardinality) (take 9 (formula 1000000))

    it "ranks a user term back at early and late ranks" $ do
        let generator = Gen.upToSize 8 (indexed 999999)
            total = sum (take 8 (formula 1000000))
            ranks = map Rank [0, 1, 2, 999999, 1000000, 1000001, 3000000000000, total - 2, total - 1]
        mapM_ (\rank -> (Gen.unrank generator rank >>= Gen.rankOfTerm generator) `shouldBe` Right rank) ranks
        Gen.unrank generator 5 `shouldBe` Right (Node "#5" [])
        Gen.unrank generator 999999 `shouldBe` Right (Node "#999999" [])

    it "gives the ranks of the listed route on 0..3, up to size 7" $ do
        let direct = Gen.upToSize 7 (indexed 3)
            reference = Gen.upToSize 7 (listed 3)
            total = either (const 0) (\(Cardinality n) -> n) (Gen.cardinality direct)
        Gen.cardinality direct `shouldBe` Gen.cardinality reference
        mapM_
            ( \rank -> do
                Gen.unrank direct rank `shouldBe` Gen.unrank reference rank
                (Gen.unrank direct rank >>= Gen.rankOfTerm direct) `shouldBe` Right rank
            )
            (everyRank (Cardinality total))
