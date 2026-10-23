{- | Value sorts in a signature: an interval and a pool, against a brute-force
enumeration, against the listed route (one constant for each value), and
against the type checker.
-}
module Data.CFTA.Gen.ValueSortsSpec (spec) where

import Data.List (sort)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Gen (Gen)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.ManySorted
import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import Data.CFTA.Term (Term (Node))

data Sort = Int | Bool | Color
    deriving (Eq, Ord, Show)

codec :: ValueCodec Sort String
codec =
    ValueCodec
        { injectInteger = \n -> '#' : show n
        , projectInteger = \symbol -> case symbol of
            '#' : digits | [(n, "")] <- reads digits -> Just n
            _ -> Nothing
        , valueSymbol = \s -> '<' : show s <> ">"
        }

-- | Int has an interval, Color has a pool. The functions use both.
valued :: Integer -> Integer -> SortedSignature Sort String
valued low high =
    SortedSignature
        { sortedSorts = [Int, Bool, Color]
        , sortedFunctions =
            [ SortedFunction "add" [Int, Int] Int
            , SortedFunction "lt" [Int, Int] Bool
            , SortedFunction "ite" [Bool, Int, Int] Int
            , SortedFunction "paint" [Color, Int] Int
            ]
        , sortedRoots = [Int, Bool]
        , sortedValues = [ValueSort Int (Interval low high), ValueSort Color (Pool ["red", "green"])]
        }

-- | The same language with one constant for each value.
expanded :: SortedSignature Sort String -> SortedSignature Sort String
expanded signature =
    signature
        { sortedFunctions = sortedFunctions signature <> concatMap constants (sortedValues signature)
        , sortedValues = []
        }
  where
    constants (ValueSort sort' (Interval low high)) = [SortedFunction (injectInteger codec n) [] sort' | n <- [low .. high]]
    constants (ValueSort sort' (Pool symbols)) = [SortedFunction symbol [] sort' | symbol <- symbols]

maxSize :: Int
maxSize = 7

bounded :: SortedSignature Sort String -> Gen String (Term String)
bounded signature = either (error . show) (Gen.upToSize (fromIntegral maxSize)) (signatureGenWith codec signature)

members :: Gen String (Term String) -> [Term String]
members = either (error . show) id . Gen.values

-- | Every term of a sort with exactly the given number of nodes.
bruteForce :: SortedSignature Sort String -> Sort -> Int -> [Term String]
bruteForce signature = terms
  where
    terms sort' size =
        [ Node (functionSymbol function) children
        | function <- sortedFunctions signature
        , functionResult function == sort'
        , children <- arguments (functionArguments function) (size - 1)
        ]
    arguments [] 0 = [[]]
    arguments [] _ = []
    arguments (argument : rest) budget =
        [ first : others
        | firstSize <- [1 .. budget]
        , first <- terms argument firstSize
        , others <- arguments rest (budget - firstSize)
        ]

-- | Every term with the given number of nodes, over some symbols, with any arity from zero to three.
untypedTerms :: [String] -> Int -> [Term String]
untypedTerms symbols size =
    [ Node symbol children
    | symbol <- symbols
    , arity <- [0 .. 3 :: Int]
    , children <- split arity (size - 1)
    ]
  where
    split 0 0 = [[]]
    split 0 _ = []
    split n budget =
        [ first : rest
        | firstSize <- [1 .. budget]
        , first <- untypedTerms symbols firstSize
        , rest <- split (n - 1) (budget - firstSize)
        ]

failure :: Either (SignatureError Sort String) a -> Maybe (SignatureError Sort String)
failure = either Just (const Nothing)

spec :: Spec
spec = describe "Data.CFTA.Gen.ManySorted value sorts" $ do
    let signature = valued 0 2
        oracle = expanded signature
        generator = bounded signature
        generated = members generator

    it "counts as a brute-force enumeration of the expanded signature does" $
        mapM_
            ( \size ->
                Gen.countAtSize generator (fromIntegral size)
                    `shouldBe` Right (Cardinality (fromIntegral (length (concat [bruteForce oracle root size | root <- sortedRoots oracle]))))
            )
            [1 .. maxSize]

    it "generates the terms of the expanded signature, in size order" $ do
        let reference = either (error . show) (Gen.upToSize (fromIntegral maxSize)) (signatureGen oracle)
        sort generated `shouldBe` sort (members reference)
        length generated `shouldSatisfy` (> 100)
        let sizes = map length generated
        sizes `shouldBe` sort sizes

    it "gives the ranks of the expanded signature when the values are an interval" $ do
        let intervalOnly =
                (valued 0 2)
                    { sortedFunctions = [f | f <- sortedFunctions (valued 0 2), functionSymbol f /= "paint"]
                    , sortedValues = [ValueSort Int (Interval 0 2)]
                    }
            direct = bounded intervalOnly
            reference = either (error . show) (Gen.upToSize (fromIntegral maxSize)) (signatureGen (expanded intervalOnly))
        Gen.cardinality direct `shouldBe` Gen.cardinality reference
        mapM_
            (\rank -> Gen.unrank direct rank `shouldBe` Gen.unrank reference rank)
            (everyRank (Cardinality (fromIntegral (length (members direct)))))

    it "ranks every generated term back" $
        mapM_
            (\rank -> (Gen.unrank generator rank >>= Gen.rankOfTerm generator) `shouldBe` Right rank)
            (everyRank (Cardinality (fromIntegral (length generated))))

    it "type checks every generated term, and agrees with the expanded signature on untyped terms" $ do
        mapM_
            (\term -> typeCheckWith codec signature term `shouldSatisfy` either (const False) (`elem` sortedRoots signature))
            generated
        let symbols = ["add", "lt", "ite", "paint", "#0", "#2", "#3", "#-1", "red", "green", "blue", "<Int>", "<Color>"]
            untyped = concatMap (untypedTerms symbols) [1 .. 4]
        length untyped `shouldSatisfy` (> 1000)
        mapM_ (\term -> (term, typeCheckWith codec signature term) `shouldBe` (term, typeCheck oracle term)) untyped

    it "rejects a value outside its source and a value with a child" $ do
        typeCheckWith codec signature (Node "add" [Node "#0" [], Node "#3" []])
            `shouldSatisfy` either (\err -> case err of UnknownFunction _ "#3" -> True; _ -> False) (const False)
        typeCheckWith codec signature (Node "#1" [Node "#0" []])
            `shouldSatisfy` either (\err -> case err of WrongArity _ "#1" 0 1 -> True; _ -> False) (const False)

    it "ranks a million values at early and late ranks" $ do
        let big = (valued 0 999999){sortedValues = [ValueSort Int (Interval 0 999999), ValueSort Color (Pool ["red", "green"])]}
            generatorBig = either (error . show) (Gen.upToSize 5) (signatureGenWith codec big)
            total = either (const 0) (\(Cardinality n) -> n) (Gen.cardinality generatorBig)
            ranks = map Rank [0, 1, 999999, 1000000, total `div` 2, total - 2, total - 1]
        Gen.countAtSize generatorBig 1 `shouldBe` Right (Cardinality 1000000)
        mapM_
            ( \rank -> do
                (Gen.unrank generatorBig rank >>= Gen.rankOfTerm generatorBig) `shouldBe` Right rank
                either
                    (const False)
                    (\term -> either (const False) (const True) (typeCheckWith codec big term))
                    (Gen.unrank generatorBig rank)
                    `shouldBe` True
            )
            ranks

    it "reports a bad value sort" $ do
        failure (signatureGenWith codec signature{sortedValues = sortedValues signature <> [ValueSort Int (Interval 5 6)]})
            `shouldBe` Just (DuplicateValueSort Int)
        failure (signatureGenWith codec signature{sortedValues = [ValueSort Int (Interval 3 2)]})
            `shouldBe` Just (EmptyValueSource Int)
        failure (signatureGenWith codec signature{sortedValues = [ValueSort Int (Pool [])]})
            `shouldBe` Just (EmptyValueSource Int)
        failure (signatureGenWith codec signature{sortedFunctions = SortedFunction "#1" [] Int : sortedFunctions signature})
            `shouldBe` Just (DuplicateSymbol "#1")
        failure (signatureGenWith codec signature{sortedValues = [ValueSort Int (Interval 0 5), ValueSort Color (Pool ["#4"])]})
            `shouldBe` Just (DuplicateSymbol "#4")
        failure (signatureGenWith codec signature{sortedSorts = [Int, Bool]}) `shouldBe` Just (UnknownSort Color)
        failure (signatureGen signature) `shouldBe` Just ValueSortsNeedCodec
