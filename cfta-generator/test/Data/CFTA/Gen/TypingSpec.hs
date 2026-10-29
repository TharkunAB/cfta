{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE QualifiedDo #-}

{- | Typed languages from typing rules, against a hand-written automaton and
against recurrences that count the closed well-typed terms.
-}
module Data.CFTA.Gen.TypingSpec (spec) where

import Control.Monad (replicateM)
import Data.Containers.ListUtils (nubOrd)
import Data.List (sort)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isNothing)
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, conjoinConstraints, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Refinement.Derive (NodeView)
import Data.CFTA.Gen.TypedArithmeticLanguage
import Data.CFTA.Gen.Typing (
    Bound (..),
    Rule,
    Typing (Typing),
    TypingError (..),
    TypingState (Goal),
    fromConstructorAutomaton,
    fromTypingRules,
    rule,
    subterm,
    value,
    variable,
 )
import qualified Data.CFTA.Gen.Typing.Do as Typing
import Data.CFTA.Generic (
    Constructor (..),
    HasFTA (..),
    annotateConstructors,
    constructorLabel,
    datatypeFTA,
    decodeLabelledTerm,
    deriveFTA,
    deriveFTAWith,
    domain,
 )
import Data.CFTA.Index (Cardinality (..), Rank (..), Size (..))
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (path)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..), excludeAnywhereFTA)
import qualified Data.CFTA.Term as Term

-- * The language of the binders spike

-- | Two types.
data Ty = TInt | TBool
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | Typed terms with de Bruijn variables. A variable carries its type.
data Typed = TZero | TTrue | TAdd Typed Typed | TIsZero Typed | TVar !Int !Ty | TLet Typed Typed
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | One node of a 'Typed' term, for the typing rules.
data TypedNode e = TZeroNode | TTrueNode | TAddNode e e | TIsZeroNode e | TVarNode e e | TLetNode e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The typing rules of 'Typed'.
typedRules :: [Rule TypedNode Ty]
typedRules =
    [ rule TZeroNode TInt
    , rule TTrueNode TBool
    , rule (TAddNode (subterm [] TInt) (subterm [] TInt)) TInt
    , rule (TIsZeroNode (subterm [] TInt)) TBool
    , variable (\index typ -> TVarNode (value index) (value typ))
    ]
        <> [rule (TLetNode (subterm [] rhs) (subterm [rhs] typ)) typ | rhs <- [TInt, TBool], typ <- [TInt, TBool]]

-- | The typing rules of 'Typed' in the do-notation of "Data.CFTA.Gen.Typing.Do".
typedRulesDo :: [Rule TypedNode Ty]
typedRulesDo =
    [rule TZeroNode TInt, rule TTrueNode TBool]
        <> Typing.do
            left <- Typing.sub TInt
            right <- Typing.sub TInt
            Typing.yields (TAddNode left right) TInt
        <> Typing.do
            argument <- Typing.sub TInt
            Typing.yields (TIsZeroNode argument) TBool
        <> [variable (\index typ -> TVarNode (value index) (value typ))]
        <> Typing.do
            rhs <- Typing.each [TInt, TBool]
            typ <- Typing.each [TInt, TBool]
            bound <- Typing.sub rhs
            body <- Typing.under [rhs] typ
            Typing.yields (TLetNode bound body) typ

-- | The closed well-typed terms up to the bound, from the rules.
typedLanguage :: Int -> Gen.Gen Symbol Typed
typedLanguage = typedPrograms []

-- | The well-typed terms over the inputs up to the bound, from the rules.
typedPrograms :: [Ty] -> Int -> Gen.Gen Symbol Typed
typedPrograms inputTypes bound =
    either (error . show) id $ fromTypingRules (Typing (Nesting (fromIntegral bound)) inputTypes [TInt, TBool] typedRules)

{- | The number of well-typed terms over the inputs up to the bound, from a
recurrence over the environment: @count n env typ@ is the number of terms of
the type in the environment with a nesting of at most @n@.
-}
typedCount :: [Ty] -> Int -> Integer
typedCount inputTypes bound = count bound inputTypes TInt + count bound inputTypes TBool
  where
    leaves env typ = 1 + fromIntegral (length (filter (== typ) env))
    count :: Int -> [Ty] -> Ty -> Integer
    count 0 env typ = leaves env typ
    count n env typ =
        leaves env typ
            + operator
            + sum [count (n - 1) env rhs * count (n - 1) (rhs : env) typ | rhs <- [TInt, TBool]]
      where
        operator = case typ of
            TInt -> count (n - 1) env TInt * count (n - 1) env TInt
            TBool -> count (n - 1) env TInt

-- | The type of a typed term in an environment, if it has one.
typeOf :: [Ty] -> Typed -> Maybe Ty
typeOf _ TZero = Just TInt
typeOf _ TTrue = Just TBool
typeOf env (TAdd left right) = do
    TInt <- typeOf env left
    TInt <- typeOf env right
    Just TInt
typeOf env (TIsZero inner) = do
    TInt <- typeOf env inner
    Just TBool
typeOf env (TVar index typ)
    | index >= 0, index < length env, env !! index == typ = Just typ
    | otherwise = Nothing
typeOf env (TLet rhs body) = do
    rhsType <- typeOf env rhs
    typeOf (rhsType : env) body

-- | The nesting of a typed term: the constructors with subterms on the longest path.
nesting :: Typed -> Int
nesting term = case term of
    TAdd left right -> 1 + max (nesting left) (nesting right)
    TIsZero inner -> 1 + nesting inner
    TLet rhs body -> 1 + max (nesting rhs) (nesting body)
    _ -> 0

-- | A state of the hand-written automaton (path (b) of the binders spike).
data State = HandRoot | HandTyping ![Ty] !Ty !Int | Index !Int | TypeState !Ty
    deriving stock (Eq, Ord, Show)

{- | The hand-written automaton of the closed typed terms up to the bound,
over the labels of the constructors of 'Typed'.
-}
explicitTyped :: Int -> FTA.FTA State String Constraint
explicitTyped bound = either (error . show) id $ FTA.mkFTA HandRoot rows
  where
    derived = either (error . show) id $ deriveFTAWith @Typed (domain [0 .. bound - 1 :: Int])
    labels =
        Map.fromList
            [ (constructorName constructor, constructorLabel constructor)
            | transitions <- Map.elems (FTA.transitionTable (datatypeFTA derived))
            , FTA.Transition constructor _ _ <- transitions
            ]
    label name = Map.findWithDefault (error ("no constructor " <> name)) name labels
    transition name children = FTA.Transition (label name) children noConstraint
    reachable = closure [] [HandTyping [] TInt bound, HandTyping [] TBool bound]
    closure seen [] = seen
    closure seen (state : pending)
        | state `elem` seen = closure seen pending
        | otherwise = closure (state : seen) (concatMap FTA.transitionChildren (row state) <> pending)
    rows =
        (HandRoot, row (HandTyping [] TInt bound) <> row (HandTyping [] TBool bound))
            : [(state, row state) | state <- reachable]
    row HandRoot = []
    row (Index index) = [transition (show index) []]
    row (TypeState typ) = [transition (show typ) []]
    row (HandTyping env typ remaining) =
        [transition "TZero" [] | typ == TInt]
            <> [transition "TTrue" [] | typ == TBool]
            <> [transition "TVar" [Index index, TypeState typ] | (index, bound') <- zip [0 ..] env, bound' == typ]
            <> concat
                [ [transition "TAdd" [HandTyping env TInt below, HandTyping env TInt below] | typ == TInt]
                    <> [transition "TIsZero" [HandTyping env TInt below] | typ == TBool]
                    <> [transition "TLet" [HandTyping env rhs below, HandTyping (rhs : env) typ below] | rhs <- [TInt, TBool]]
                | remaining > 0
                , let below = remaining - 1
                ]

-- | The closed typed terms of the hand-written automaton up to the bound.
handWritten :: Int -> Gen.Gen String Typed
handWritten bound = decode <$> Gen.fromAutomaton (Interned.fromFTA (explicitTyped bound))
  where
    derived = either (error . show) id $ deriveFTAWith @Typed (domain [0 .. bound - 1 :: Int])
    decode term = fromMaybe (error ("a term that does not decode: " <> show term)) (decodeLabelledTerm derived term)

-- * Typed arithmetic

-- | Arithmetic with literals and three binary operators.
data Arithmetic = Number Int | Add Arithmetic Arithmetic | Subtract Arithmetic Arithmetic | Multiply Arithmetic Arithmetic
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | One node of an arithmetic term, for its typing rules.
data ArithmeticNode e = NumberNode e | AddNode e e | SubtractNode e e | MultiplyNode e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The typed arithmetic over the inputs up to the bound, with the inputs as variables or as arguments.
arithPrograms :: [ArithType] -> [ArithType] -> Int -> Gen.Gen Symbol Arith
arithPrograms inputTypes argumentTypes bound =
    either (error . show) id $
        fromTypingRules (Typing (Nesting (fromIntegral bound)) inputTypes [IntType, BoolType] withArguments)
  where
    withArguments = arithRules <> [rule (ArgNode (value position)) typ | (position, typ) <- zip [0 :: Int ..] argumentTypes]

-- | Whether each conditional of the type 'IntType' in a well-typed term has two equal branches.
equalIntBranches :: [ArithType] -> Arith -> Bool
equalIntBranches env term = case term of
    If condition yes no -> (arithType env yes /= Just IntType || yes == no) && all (equalIntBranches env) [condition, yes, no]
    Plus left right -> equalIntBranches env left && equalIntBranches env right
    Less left right -> equalIntBranches env left && equalIntBranches env right
    Let rhs body -> equalIntBranches env rhs && equalIntBranches (fromMaybe (error "an ill-typed term") (arithType env rhs) : env) body
    _ -> True

-- | The number of well-typed arithmetic terms over the inputs up to the bound, from a recurrence over the environment.
arithCount :: [ArithType] -> Int -> Integer
arithCount inputTypes bound = count bound inputTypes IntType + count bound inputTypes BoolType
  where
    leaves env typ = 2 + fromIntegral (length (filter (== typ) env))
    count :: Int -> [ArithType] -> ArithType -> Integer
    count 0 env typ = leaves env typ
    count n env typ =
        leaves env typ
            + below env IntType * below env IntType
            + below env BoolType * below env typ * below env typ
            + sum [below env rhs * below (rhs : env) typ | rhs <- [IntType, BoolType]]
      where
        below = count (n - 1)

-- * A bound on the binders

-- | The typed arithmetic with at most the binders around each position, over the inputs.
arithBinders :: [ArithType] -> Int -> Gen.Gen Symbol Arith
arithBinders inputTypes limit =
    either (error . show) id $ fromTypingRules (Typing (Binders limit) inputTypes [IntType, BoolType] arithRules)

-- | The spike's language with at most the binders around each position, over the inputs.
typedBinders :: [Ty] -> Int -> Gen.Gen Symbol Typed
typedBinders inputTypes limit =
    either (error . show) id $ fromTypingRules (Typing (Binders limit) inputTypes [TInt, TBool] typedRules)

{- | The number of well-typed arithmetic terms of each size from 1 to the
size, with at most the binders around each position, over the inputs. The
size is the number of term nodes: a literal, a flag, and a variable have two.
-}
arithSizeCounts :: [ArithType] -> Int -> Int -> [Integer]
arithSizeCounts inputTypes limit largest = [count size inputTypes IntType + count size inputTypes BoolType | size <- [1 .. largest]]
  where
    types = [IntType, BoolType]
    count size env typ = LazyMap.findWithDefault 0 (size, env, typ) table
    table =
        LazyMap.fromList
            [ ((size, env, typ), counted size env typ)
            | size <- [0 .. largest]
            , binders <- [0 .. limit]
            , bound' <- replicateM binders types
            , let env = bound' <> inputTypes
            , typ <- types
            ]
    counted size env typ =
        sum
            [ if size == 2 then 2 + fromIntegral (length (filter (== typ) env)) else 0
            , pairs (size - 1) env IntType IntType
            , sum [count condition env BoolType * count yes env typ * count no env typ | (condition, yes, no) <- triples (size - 1)]
            , sum
                [ count rhsSize env rhs * count bodySize (rhs : env) typ
                | length env - length inputTypes < limit
                , rhs <- types
                , (rhsSize, bodySize) <- splits (size - 1)
                ]
            ]
    pairs size env left right = sum [count leftSize env left * count rightSize env right | (leftSize, rightSize) <- splits size]
    splits size = [(left, size - left) | left <- [1 .. size - 1]]
    triples size = [(first, second, size - first - second) | first <- [1 .. size - 2], second <- [1 .. size - first - 1]]

{- | The number of well-typed terms of the spike's language of each size from 1
to the size, with at most the binders around each position, over the inputs.
A variable has three nodes: the variable, its index, and its type.
-}
typedSizeCounts :: [Ty] -> Int -> Int -> [Integer]
typedSizeCounts inputTypes limit largest = [count size inputTypes TInt + count size inputTypes TBool | size <- [1 .. largest]]
  where
    types = [TInt, TBool]
    count size env typ = LazyMap.findWithDefault 0 (size, env, typ) table
    table =
        LazyMap.fromList
            [ ((size, env, typ), counted size env typ)
            | size <- [0 .. largest]
            , binders <- [0 .. limit]
            , bound' <- replicateM binders types
            , let env = bound' <> inputTypes
            , typ <- types
            ]
    counted size env typ =
        sum
            [ if size == 1 then 1 else 0
            , if size == 3 then fromIntegral (length (filter (== typ) env)) else 0
            , case typ of
                TInt -> sum [count left env TInt * count (size - 1 - left) env TInt | left <- [1 .. size - 2]]
                TBool -> count (size - 1) env TInt
            , sum
                [ count rhsSize env rhs * count (size - 1 - rhsSize) (rhs : env) typ
                | length env - length inputTypes < limit
                , rhs <- types
                , rhsSize <- [1 .. size - 2]
                ]
            ]

-- | The largest number of binders around a position of an arithmetic term.
arithBinderDepth :: Arith -> Int
arithBinderDepth term = case term of
    Let rhs body -> max (arithBinderDepth rhs) (1 + arithBinderDepth body)
    _ -> maximum (0 : map arithBinderDepth (drop 1 (subterms' term)))
  where
    subterms' current =
        current : case current of
            Plus left right -> [left, right]
            Less left right -> [left, right]
            If condition yes no -> [condition, yes, no]
            _ -> []

-- | The number of term nodes of a value.
termSize :: (HasFTA v) => v -> Int
termSize = length . encodeTerm

-- | The counts of a recursive generator at each size from 1 to the size.
countsUpTo :: Int -> Gen.Gen symbol a -> [Integer]
countsUpTo largest generator =
    [ either (error . show) (\(Cardinality count) -> count) (Gen.countAtSize generator (Size (fromIntegral size)))
    | size <- [1 .. largest]
    ]

-- * Inspection

-- | The cardinality of a generator.
total :: Gen.Gen symbol a -> Integer
total generator = case Gen.cardinality generator of
    Right (Cardinality count) -> count
    Left err -> error (show err)

-- | The members of a generator, in order.
members :: (Ord a) => Gen.Gen symbol a -> [a]
members = sort . either (error . show) id . Gen.values

-- * A choice that reads an earlier one

-- | A fraction of two literals.
data Fraction = Frac !Int !Int
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | The node of a 'Fraction'.
data FractionNode e = FracNode e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | The fractions of a number from 1 to 12 by one of its divisors.
fractionRules :: [Rule FractionNode ()]
fractionRules = Typing.do
    n <- Typing.each [1 .. 12 :: Int]
    d <- Typing.each [1 .. n]
    Typing.guard (n `mod` d == 0)
    Typing.yields (FracNode (value n) (value d)) ()

-- * The order of a helper type

-- | A helper type. Its constructors are declared in the reverse order of their labels.
data Letter = Z | A
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | A language with one constructor, whose field has the helper type.
newtype Lettered = Lit Letter
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | The node of a 'Lettered' term.
newtype LetteredNode e = LitNode e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | A non-regular type: each level nests its element type in a list.
data Nested a = Here a | Deeper (Nested [a])
    deriving stock (Eq, Ord, Show, Generic)

instance (HasFTA a) => HasFTA (Nested a)

-- | A language with a field of the non-regular type, which no rule uses.
data Holding = Plain | Other | Holder (Nested Int)
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | The node of a 'Holding' term.
data HoldingNode e = PlainNode | OtherNode | HolderNode e
    deriving stock (Generic)
    deriving anyclass (NodeView)

spec :: Spec
spec = describe "Data.CFTA.Gen.Typing" $ do
    describe "the language of the binders spike" $ do
        it "gives the members of the hand-written automaton up to the bounds 2 and 3" $ do
            members (typedLanguage 2) `shouldBe` members (handWritten 2)
            members (typedLanguage 3) `shouldBe` members (handWritten 3)
            length (members (typedLanguage 2)) `shouldBe` 222
        it "counts the terms of the recurrence up to the bound 6" $
            map (total . typedLanguage) [0 .. 6] `shouldBe` map (typedCount []) [0 .. 6]
        it "gives each value the rank of its term" $ do
            let generator = typedLanguage 2
            mapM (Gen.rankOfValue generator) (either (error . show) id (Gen.values generator))
                `shouldBe` Right (map Rank [0 .. total generator - 1])
    describe "typed arithmetic" $ do
        it "ranks 6 * 7 before a zero-padded term in size order without removing terms" $ do
            let rules =
                    [rule (NumberNode (value n)) IntType | n <- [0, 6, 7 :: Int]]
                        <> [ rule (operator (subterm [] IntType) (subterm [] IntType)) IntType
                           | operator <- [AddNode, SubtractNode, MultiplyNode]
                           ]
                small = Multiply (Number 6) (Number 7)
                padded = Add (Add (Number 0) (Subtract (Number 0) (Number 0))) small
            original <- either (fail . show) pure $ fromTypingRules @Arithmetic (Typing (Nesting 3) [] [IntType] rules)
            let ordered = Gen.upToSize 23 original
            originalSmall <- either (fail . show) pure $ Gen.rankOfValue original small
            originalPadded <- either (fail . show) pure $ Gen.rankOfValue original padded
            originalSmall `shouldSatisfy` (> originalPadded)
            smallRank <- either (fail . show) pure $ Gen.rankOfValue ordered small
            paddedRank <- either (fail . show) pure $ Gen.rankOfValue ordered padded
            smallRank `shouldSatisfy` (< paddedRank)
            Gen.cardinality ordered `shouldBe` Gen.cardinality original
            Gen.unrank ordered smallRank `shouldBe` Right small
            Gen.unrank ordered paddedRank `shouldBe` Right padded
            Gen.sizeOfRank ordered smallRank `shouldBe` Just 5
            Gen.sizeOfRank ordered paddedRank `shouldBe` Just 14
        it "counts the terms of the recurrence up to the bound 6" $
            map (total . arithLanguage) [0 .. 6] `shouldBe` map (arithCount []) [0 .. 6]
        it "gives distinct well-typed terms of a nesting up to the bound 2, as many as the recurrence" $ do
            let listed = either (error . show) id (Gen.values (arithLanguage 2))
            filter (isNothing . arithType []) listed `shouldBe` []
            filter ((> 2) . arithNesting) listed `shouldBe` []
            length (nubOrd listed) `shouldBe` length listed
            fromIntegral (length listed) `shouldBe` arithCount [] 2
        it "decodes sampled ranks to well-typed terms up to the bound 3, and ranks them back" $ do
            let generator = arithLanguage 3
                count = total generator
                ranks = [Rank (index * (count - 1) `div` 199) | index <- [0 .. 199]]
                decoded = either (error . show) id (mapM (Gen.unrank generator) ranks)
            filter (isNothing . arithType []) decoded `shouldBe` []
            filter ((> 3) . arithNesting) decoded `shouldBe` []
            mapM (Gen.rankOfValue generator) decoded `shouldBe` Right ranks
    describe "inputs" $ do
        it "count the programs over the inputs as the recurrence does up to the bound 6" $ do
            map (total . typedPrograms [TInt, TBool]) [0 .. 6] `shouldBe` map (typedCount [TInt, TBool]) [0 .. 6]
            map (total . arithPrograms [IntType, BoolType] []) [0 .. 6] `shouldBe` map (arithCount [IntType, BoolType]) [0 .. 6]
        it "give distinct programs that type-check in the inputs, of a nesting up to the bound 2, as many as the recurrence" $ do
            let listed = either (error . show) id (Gen.values (typedPrograms [TInt, TBool] 2))
            filter (isNothing . typeOf [TInt, TBool]) listed `shouldBe` []
            filter ((> 2) . nesting) listed `shouldBe` []
            length (nubOrd listed) `shouldBe` length listed
            fromIntegral (length listed) `shouldBe` typedCount [TInt, TBool] 2
        it "count as arguments that are static rules, which binders do not move" $
            map (total . arithPrograms [] [IntType, BoolType]) [0 .. 5] `shouldBe` map (arithCount [IntType, BoolType]) [0 .. 5]
    describe "the automaton" $ do
        let derived = either (error . show) id $ deriveFTAWith @Arith (domain [0, 1 :: Int])
            same left right = if left == right then Just left else Nothing
            listed = either (error . show) id . Gen.values
        it "reads the grammar of a datatype in the ranks of fromDatatypeUpToDepth" $ do
            let typedGrammar = either (error . show) id $ deriveFTAWith @Typed (domain [0, 1 :: Int])
            listed (fromConstructorAutomaton @Typed (FTA.boundDepth 2 (datatypeFTA typedGrammar)))
                `shouldBe` listed (Gen.fromDatatypeUpToDepth 2 typedGrammar)
        it "keeps the terms whose sums add equal terms, in a product with an annotated grammar" $ do
            let equalOperands = equalityConstraint (mkEqConstraints [[path [0], path [1]]])
                annotated = either (error . show) id $ annotateConstructors noConstraint [("Plus", equalOperands)] derived
                product' = FTA.intersectWith same conjoinConstraints (arithAutomaton 2) (datatypeFTA annotated)
                equalSums term = and [left == right | Plus left right <- subterms term]
            members (fromConstructorAutomaton @Arith product') `shouldBe` filter equalSums (members (arithLanguage 2))
        it "keeps the terms without a subterm that a template matches" $ do
            let constructorOf :: (HasFTA v) => v -> Constructor
                constructorOf = Term.rootLabel . encodeTerm
                template =
                    TemplateNode
                        (constructorOf (Plus (Num 0) (Num 0)))
                        [TemplateNode (constructorOf (Num 0)) [TemplateNode (constructorOf (0 :: Int)) []], Hole]
                excluded = excludeAnywhereFTA [template] (arithAutomaton 2)
                addsZero term = not (null [() | Plus (Num 0) _ <- subterms term])
            members (fromConstructorAutomaton @Arith excluded) `shouldBe` filter (not . addsZero) (members (arithLanguage 2))
        it "can read the types of the states in an annotation" $ do
            -- A conditional of the type IntType has a child state of that type.
            let equalBranches = equalityConstraint (mkEqConstraints [[path [1], path [2]]])
                annotation _ (FTA.Transition constructor children _) = case children of
                    [_, Goal _ IntType _, _] | constructorName constructor == "If" -> equalBranches
                    _ -> noConstraint
                annotated = FTA.annotate annotation (arithAutomaton 2)
            members (fromConstructorAutomaton @Arith annotated) `shouldBe` filter (equalIntBranches []) (members (arithLanguage 2))
    describe "a bound on the binders" $ do
        it "counts the terms of each size as a recurrence does, for both languages" $ do
            mapM_
                (\limit -> countsUpTo 12 (arithBinders [] limit) `shouldBe` arithSizeCounts [] limit 12)
                [0, 1, 2]
            mapM_
                (\limit -> countsUpTo 12 (typedBinders [] limit) `shouldBe` typedSizeCounts [] limit 12)
                [0, 1, 2]
        it "counts the programs over inputs, which are not binders" $
            countsUpTo 12 (typedBinders [TInt, TBool] 1) `shouldBe` typedSizeCounts [TInt, TBool] 1 12
        it "gives distinct well-typed terms up to a size with the binders, as many as the recurrence" $ do
            let listed = either (error . show) id (Gen.values (Gen.upToSize 11 (arithBinders [] 1)))
            filter (isNothing . arithType []) listed `shouldBe` []
            filter ((> 1) . arithBinderDepth) listed `shouldBe` []
            filter ((> 11) . termSize) listed `shouldBe` []
            length (nubOrd listed) `shouldBe` length listed
            fromIntegral (length listed) `shouldBe` sum (arithSizeCounts [] 1 11)
    describe "the rules" $ do
        it "take a node view that fits the datatype" $
            either Just (const Nothing) (fromTypingRules @Arith (Typing (Nesting 1) [] [IntType] [rule TZeroNode IntType]))
                `shouldBe` Just (NodeViewMismatch "Num Flag Plus Less If Var Let Arg" "the datatype has 8 constructors, the node view 6")
        it "take a bound that is not negative" $ do
            let failure bound = either Just (const Nothing) (fromTypingRules @Arith (Typing bound [] [IntType] arithRules))
            failure (Nesting (-1)) `shouldBe` Just (NegativeBound (Nesting (-1)))
            failure (Binders (-1)) `shouldBe` Just (NegativeBound (Binders (-1)))
            failure (Nesting 0) `shouldBe` Nothing
        it "fit the fields of their constructor" $ do
            let mismatch :: [Rule ArithNode ArithType] -> Maybe TypingError
                mismatch given = either Just (const Nothing) (fromTypingRules @Arith (Typing (Nesting 1) [] [IntType] given))
            mismatch [rule (NumNode (subterm [] IntType)) IntType] `shouldBe` Just (FieldMismatch "Num")
            mismatch [rule (NumNode (value True)) IntType] `shouldBe` Just (FieldMismatch "Num")
            mismatch [rule (LetNode (value (Var 99)) (subterm [IntType] IntType)) IntType] `shouldBe` Just (FieldMismatch "Let")
            mismatch [rule (LetNode (value (Plus (Num 0) (Num 0))) (subterm [IntType] IntType)) IntType]
                `shouldBe` Just (FieldMismatch "Let")
            mismatch [rule (LetNode (value (0 :: Int)) (subterm [IntType] IntType)) IntType] `shouldBe` Just (FieldMismatch "Let")
            mismatch
                [ rule (NumNode (value (0 :: Int))) IntType
                , rule (LetNode (subterm [] IntType) (subterm [IntType] IntType)) IntType
                , variable (\_ _ -> VarNode (value False))
                ]
                `shouldBe` Just (FieldMismatch "Var")
    describe "the do-notation" $ do
        it "gives the language of the same rules in a list, in the same order" $
            Gen.values (either (error . show) id (fromTypingRules @Typed (Typing (Nesting 2) [] [TInt, TBool] typedRulesDo)))
                `shouldBe` Gen.values (typedLanguage 2)
        it "reads earlier choices, and keeps the combinations that the guard accepts" $ do
            let fractions = fromTypingRules @Fraction (Typing (Nesting 0) [] [()] fractionRules)
                expected = [Frac n d | n <- [1 .. 12], d <- [1 .. n], n `mod` d == 0]
            fmap sort (Gen.values (either (error . show) id fractions)) `shouldBe` Right (sort expected)
            length expected `shouldBe` 35
    describe "the order of the values" $ do
        it "orders the constructors of a helper type in declaration order, as fromDatatype does" $ do
            let typed =
                    either (error . show) id $
                        fromTypingRules @Lettered (Typing (Nesting 0) [] [()] [rule (LitNode (value A)) (), rule (LitNode (value Z)) ()])
                derived = Gen.fromDatatype $ either (error . show) id $ deriveFTA @Lettered
            Gen.values derived `shouldBe` Right [Lit Z, Lit A]
            Gen.values typed `shouldBe` Right [Lit Z, Lit A]
        it "reads only the types of the rules, so a non-regular field that no rule uses does not stop it" $
            Gen.values
                ( either (error . show) id $
                    fromTypingRules @Holding (Typing (Nesting 0) [] [()] [rule OtherNode (), rule PlainNode ()])
                )
                `shouldBe` Right [Plain, Other]
