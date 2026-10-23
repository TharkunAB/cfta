{- | Terms of a run-time signature against a brute-force enumeration, the type
checker, and the rank round trip.
-}
module Data.CFTA.Gen.ManySortedSpec (spec) where

import Data.List (sort)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.Either (isRight)

import qualified Data.CFTA as FTA
import Data.CFTA.Gen (Gen)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.ManySorted
import Data.CFTA.Index (Cardinality (..), everyRank)
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Term (Term (Node))

data Sort = Int | Bool
    deriving (Eq, Ord, Show)

type Signature = SortedSignature Sort String

-- | Sorts Int and Bool, with zero, one, add, lt, and ite.
arithmetic :: Signature
arithmetic =
    SortedSignature
        { sortedSorts = [Int, Bool]
        , sortedFunctions =
            [ SortedFunction "zero" [] Int
            , SortedFunction "one" [] Int
            , SortedFunction "add" [Int, Int] Int
            , SortedFunction "lt" [Int, Int] Bool
            , SortedFunction "ite" [Bool, Int, Int] Int
            ]
        , sortedRoots = [Int, Bool]
        , sortedValues = []
        }

maxSize :: Int
maxSize = 8

-- | Every term of a sort with exactly the given number of nodes.
bruteForce :: Signature -> Sort -> Int -> [Term String]
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

bounded :: Signature -> Gen String (Term String)
bounded signature = case signatureGen signature of
    Right generator -> Gen.upToSize (fromIntegral maxSize) generator
    Left err -> error (show err)

members :: Gen String (Term String) -> [Term String]
members generator = either (error . show) id (Gen.values generator)

-- | Every term with the given number of nodes, over the symbols of the signature and one more, with any arity from zero to three.
untypedTerms :: Int -> [Term String]
untypedTerms size =
    [ Node symbol children
    | symbol <- ["zero", "one", "add", "lt", "ite", "foo"]
    , arity <- [0 .. 3]
    , children <- split arity (size - 1)
    ]
  where
    split 0 0 = [[]]
    split 0 _ = []
    split n budget =
        [ first : rest
        | firstSize <- [1 .. budget]
        , first <- untypedTerms firstSize
        , rest <- split (n - 1 :: Int) (budget - firstSize)
        ]

spec :: Spec
spec = describe "Data.CFTA.Gen.ManySorted" $ do
    let generator = bounded arithmetic
        generated = members generator
        expected size = concat [bruteForce arithmetic root size | root <- sortedRoots arithmetic]

    it "type checks every generated term with a root sort" $ do
        length generated `shouldSatisfy` (> 100)
        mapM_
            (\term -> typeCheck arithmetic term `shouldSatisfy` either (const False) (`elem` sortedRoots arithmetic))
            generated

    it "counts as many terms of each size as a brute-force enumeration" $
        mapM_
            ( \size ->
                Gen.countAtSize generator (fromIntegral size) `shouldBe` Right (Cardinality (fromIntegral (length (expected size))))
            )
            [1 .. maxSize]

    it "generates exactly the brute-force terms, smaller terms first" $ do
        sort generated `shouldBe` sort (concatMap expected [1 .. maxSize])
        length (Set.toList (Set.fromList generated)) `shouldBe` length generated
        let sizes = map length generated
        sizes `shouldBe` sort sizes

    it "gives rank back for every term" $
        mapM_
            ( \rank -> do
                let decoded = Gen.unrank generator rank
                (decoded >>= Gen.rankOfTerm generator) `shouldBe` Right rank
            )
            (everyRank (Cardinality (fromIntegral (length generated))))

    it "rejects a symbol that is not in the signature at its path" $
        typeCheck
            arithmetic
            (Node "add" [Node "zero" [], Node "ite" [Node "lt" [Node "zero" [], Node "foo" []], Node "zero" [], Node "zero" []]])
            `shouldBe` Left (UnknownFunction (path [ChildIndex 1, ChildIndex 0, ChildIndex 1]) "foo")

    it "rejects a wrong number of children" $
        typeCheck
            arithmetic
            (Node "ite" [Node "lt" [Node "zero" [], Node "zero" []], Node "add" [Node "zero" []], Node "zero" []])
            `shouldBe` Left (WrongArity (path [ChildIndex 1]) "add" 2 1)

    it "rejects children of the wrong sorts at the parent" $
        typeCheck arithmetic (Node "add" [Node "zero" [], Node "lt" [Node "zero" [], Node "zero" []]])
            `shouldBe` Left (WrongChildSort (path []) "add" [Int, Int] [Just Int, Just Bool])

    it "names the first node in preorder when a parent and a later child are in error" $
        typeCheck arithmetic (Node "add" [Node "lt" [Node "zero" [], Node "zero" []], Node "foo" []])
            `shouldBe` Left (WrongChildSort (path []) "add" [Int, Int] [Just Bool, Nothing])

    it "names the child when only the child is in error" $
        typeCheck arithmetic (Node "add" [Node "zero" [], Node "add" [Node "one" [], Node "lt" [Node "one" [], Node "one" []]]])
            `shouldBe` Left (WrongChildSort (path [ChildIndex 1]) "add" [Int, Int] [Just Int, Just Bool])

    it "rejects a term whose sort is not a root sort" $
        typeCheck arithmetic{sortedRoots = [Int]} (Node "lt" [Node "zero" [], Node "zero" []])
            `shouldBe` Left (NotRootSort Bool)

    it "accepts exactly the terms that the automaton accepts, among untyped terms" $ do
        automaton <- either (fail . show) pure $ signatureAutomaton arithmetic{sortedRoots = [Bool]}
        let untyped = concatMap untypedTerms [1 .. 5]
        length untyped `shouldSatisfy` (> 1000)
        mapM_
            (\term -> (isRight (typeCheck arithmetic{sortedRoots = [Bool]} term), term) `shouldBe` (FTA.accepts automaton term, term))
            untyped
        length (filter (isRight . typeCheck arithmetic{sortedRoots = [Bool]}) untyped) `shouldSatisfy` (> 0)

    it "rejects an unknown sort" $
        failure (signatureGen arithmetic{sortedSorts = [Int]}) `shouldBe` Just (UnknownSort Bool)

    it "rejects a duplicate symbol" $
        failure (signatureGen arithmetic{sortedFunctions = SortedFunction "zero" [] Int : sortedFunctions arithmetic})
            `shouldBe` Just (DuplicateSymbol "zero")
  where
    failure = either Just (const Nothing)
