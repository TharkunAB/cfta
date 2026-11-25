{-# LANGUAGE OverloadedStrings #-}

{- | Principal sorts of a signature with sort variables: exact sorts, the
errors of the type check, the occurs check, the signature check, and a
reference that instantiates each function at closed sorts without
unification.
-}
module Data.CFTA.Gen.ManySorted.PolymorphicSpec (spec) where

import Control.Monad (foldM)
import Data.Either (isRight)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Gen.ManySorted (SortedFunction (..), TypeError (..))
import Data.CFTA.Gen.ManySorted.Polymorphic
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term (Node))

-- | The sort variables 0 and 1.
a, b :: SortTerm
a = SortVariable 0
b = SortVariable 1

int, bool :: SortTerm
int = SortApply "Int" []
bool = SortApply "Bool" []

list :: SortTerm -> SortTerm
list element = SortApply "List" [element]

pair :: SortTerm -> SortTerm -> SortTerm
pair left right = SortApply "Pair" [left, right]

-- | Table 1: zero, true, ite, eq, nil, cons, and length.
table1 :: PolymorphicSignature
table1 =
    PolymorphicSignature
        [ SortedFunction "zero" [] int
        , SortedFunction "true" [] bool
        , SortedFunction "ite" [bool, a, a] a
        , SortedFunction "eq" [a, a] bool
        , SortedFunction "nil" [] (list a)
        , SortedFunction "cons" [a, list a] (list a)
        , SortedFunction "length" [list a] int
        ]

-- | Table 2: table 1 with pair, fst, and snd.
table2 :: PolymorphicSignature
table2 =
    PolymorphicSignature $
        polymorphicFunctions table1
            <> [ SortedFunction "pair" [a, b] (pair a b)
               , SortedFunction "fst" [pair a b] a
               , SortedFunction "snd" [pair a b] b
               ]

zero, true, nil :: Term Symbol
zero = Node "zero" []
true = Node "true" []
nil = Node "nil" []

-- | The closed sorts over Int, Bool, and List, with at most three List.
closedSorts :: [SortTerm]
closedSorts = concat (take 4 (iterate (map list) [int, bool]))

{- | Every sort in 'closedSorts' of a term over 'table1'. It tries each
instance of each function at the sorts of 'closedSorts', bottom-up, and it
uses no unification. The sort of each node must be in 'closedSorts'.
-}
sortsOf :: Term Symbol -> Set.Set SortTerm
sortsOf (Node symbol children) =
    Set.fromList
        [ result
        | function <- polymorphicFunctions table1
        , functionSymbol function == symbol
        , length (functionArguments function) == length children
        , choice <- mapM (\variable -> [(variable, closed) | closed <- closedSorts]) (variablesOf function)
        , let instantiate = substituteWith (Map.fromList choice)
              result = instantiate (functionResult function)
        , result `elem` closedSorts
        , and
            (zipWith (\argument childSorts -> Set.member (instantiate argument) childSorts) (functionArguments function) childSets)
        ]
  where
    childSets = map sortsOf children
    variablesOf function = Set.toList (Set.fromList (concatMap occurrences (functionResult function : functionArguments function)))
    occurrences (SortVariable variable) = [variable]
    occurrences (SortApply _ arguments) = concatMap occurrences arguments
    substituteWith choice sortTerm = case sortTerm of
        SortVariable variable -> Map.findWithDefault sortTerm variable choice
        SortApply constructor arguments -> SortApply constructor (map (substituteWith choice) arguments)

-- | Whether a closed sort is an instance of a sort, by one-way matching.
instanceOf :: SortTerm -> SortTerm -> Bool
instanceOf general closed = isJust (match Map.empty general closed)
  where
    match bound (SortVariable variable) sortTerm = case Map.lookup variable bound of
        Nothing -> Just (Map.insert variable sortTerm bound)
        Just earlier -> if earlier == sortTerm then Just bound else Nothing
    match bound (SortApply one left) (SortApply other right)
        | one == other && length left == length right = foldM (\current (l, r) -> match current l r) bound (zip left right)
    match _ _ _ = Nothing

-- | Every term with the given number of nodes, over some symbols, with any arity from zero to three.
untypedTerms :: [Symbol] -> Int -> [Term Symbol]
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

spec :: Spec
spec = describe "Data.CFTA.Gen.ManySorted.Polymorphic" $ do
    describe "principalSort" $ do
        it "gives the principal sorts of table 1" $ do
            principalSort table1 nil `shouldBe` Right (list a)
            principalSort table1 (Node "cons" [nil, nil]) `shouldBe` Right (list (list a))
            principalSort table1 (Node "length" [nil]) `shouldBe` Right int
            principalSort table1 (Node "eq" [nil, nil]) `shouldBe` Right bool
            principalSort table1 (Node "ite" [true, nil, Node "cons" [zero, nil]]) `shouldBe` Right (list int)

        it "renames the variables of the children apart, in table 2" $ do
            principalSort table2 (Node "pair" [nil, nil]) `shouldBe` Right (pair (list a) (list b))
            principalSort table2 (Node "fst" [Node "pair" [zero, nil]]) `shouldBe` Right int
            principalSort table2 (Node "snd" [Node "pair" [zero, nil]]) `shouldBe` Right (list a)
            principalSort table2 (Node "pair" [Node "snd" [Node "pair" [zero, nil]], true]) `shouldBe` Right (pair (list a) bool)

        it "numbers the variables from 0, for any numbers in the signature" $ do
            let renumbered =
                    PolymorphicSignature
                        [ SortedFunction "zero" [] int
                        , SortedFunction "nil" [] (list (SortVariable 5))
                        , SortedFunction "pair" [SortVariable 5, SortVariable 3] (pair (SortVariable 3) (SortVariable 5))
                        ]
            principalSort renumbered nil `shouldBe` Right (list a)
            principalSort renumbered (Node "pair" [zero, nil]) `shouldBe` Right (pair (list a) int)
            principalSort renumbered (Node "pair" [nil, nil]) `shouldBe` Right (pair (list a) (list b))

        it "reports children whose sorts do not unify with the argument sorts" $ do
            principalSort table1 (Node "eq" [zero, true])
                `shouldBe` Left (WrongChildSort (path []) "eq" [a, a] [Just int, Just bool])
            principalSort table1 (Node "cons" [zero, Node "cons" [true, nil]])
                `shouldBe` Left (WrongChildSort (path []) "cons" [a, list a] [Just int, Just (list bool)])

        it "names the parent when the children with a sort do not unify, and the child otherwise" $ do
            principalSort table1 (Node "ite" [zero, Node "foo" [], zero])
                `shouldBe` Left (WrongChildSort (path []) "ite" [bool, a, a] [Just int, Nothing, Just int])
            principalSort table1 (Node "cons" [Node "eq" [zero, true], nil])
                `shouldBe` Left (WrongChildSort (path [ChildIndex 0]) "eq" [a, a] [Just int, Just bool])

        it "reports a wrong number of children and an unknown symbol" $ do
            principalSort table1 (Node "cons" [zero]) `shouldBe` Left (WrongArity (path []) "cons" 2 1)
            principalSort table1 (Node "length" [Node "foo" []]) `shouldBe` Left (UnknownFunction (path [ChildIndex 0]) "foo")

        it "makes the occurs check" $ do
            let occursTable =
                    PolymorphicSignature $
                        polymorphicFunctions table2
                            <> [SortedFunction "same" [pair a (list a)] bool, SortedFunction "dup" [a] (pair a a)]
            principalSort occursTable (Node "same" [Node "dup" [nil]])
                `shouldBe` Left (WrongChildSort (path []) "same" [pair a (list a)] [Just (pair (list a) (list a))])
            principalSort occursTable (Node "same" [Node "pair" [zero, nil]]) `shouldBe` Right bool

        it "agrees with an instantiation at closed sorts on every term up to size 5" $ do
            let symbols = map functionSymbol (polymorphicFunctions table1)
                trees = concatMap (untypedTerms symbols) [1 .. 5]
                wellSorted = filter (isRight . principalSort table1) trees
            length trees `shouldSatisfy` (> 200000)
            length wellSorted `shouldSatisfy` (> 40)
            mapM_
                ( \term -> do
                    let reference = sortsOf term
                    case principalSort table1 term of
                        Left _ -> do
                            (term, reference) `shouldBe` (term, Set.empty)
                            (term, hasSort table1 a term) `shouldBe` (term, False)
                        Right principal -> do
                            let instances = filter (instanceOf principal) closedSorts
                            (term, Set.null reference) `shouldBe` (term, False)
                            (term, Set.fromList instances) `shouldBe` (term, reference)
                            (term, filter (\closed -> hasSort table1 closed term) closedSorts) `shouldBe` (term, instances)
                            (term, hasSort table1 a term) `shouldBe` (term, True)
                )
                trees

    describe "checkPolymorphic" $
        it "rejects a repeated symbol and a sort constructor with two numbers of arguments" $ do
            checkPolymorphic table1 `shouldBe` Right ()
            checkPolymorphic table2 `shouldBe` Right ()
            checkPolymorphic (PolymorphicSignature (polymorphicFunctions table1 <> [SortedFunction "nil" [] (list int)]))
                `shouldBe` Left (RepeatedSymbol "nil")
            checkPolymorphic
                (PolymorphicSignature (polymorphicFunctions table1 <> [SortedFunction "zip" [SortApply "List" [a, b]] int]))
                `shouldBe` Left (ConstructorArity "List" 1 2)

    describe "hasSort" $
        it "tests whether a term has an instance of a sort" $ do
            hasSort table1 (list int) nil `shouldBe` True
            hasSort table1 (list bool) nil `shouldBe` True
            hasSort table1 (list a) nil `shouldBe` True
            hasSort table1 int nil `shouldBe` False
            hasSort table1 (list int) (Node "cons" [zero, nil]) `shouldBe` True
            hasSort table1 (list a) (Node "cons" [zero, nil]) `shouldBe` True
            hasSort table1 (list bool) (Node "cons" [zero, nil]) `shouldBe` False
            hasSort table1 a (Node "eq" [zero, true]) `shouldBe` False
            -- The variable 0 of the root and of the principal sort are different variables.
            hasSort table2 (pair a bool) (Node "pair" [nil, true]) `shouldBe` True
            hasSort table2 (pair a a) (Node "pair" [nil, nil]) `shouldBe` True
            hasSort table2 (pair a a) (Node "pair" [zero, true]) `shouldBe` False
