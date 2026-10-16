{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{- | Typed languages from typing rules, against a hand-written automaton and
against recurrences that count the closed well-typed terms.
-}
module Data.CFTA.Gen.TypingSpec (spec) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isNothing)
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, conjoinConstraints, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Gen as Gen
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
    typingAutomaton,
    value,
    variable,
 )
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
import Data.CFTA.Index (Cardinality (..), Rank (..))
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

-- | The typing rules of 'Typed'.
typedRules :: [Rule Ty]
typedRules =
    [ rule "TZero" [] TInt
    , rule "TTrue" [] TBool
    , rule "TAdd" [subterm [] TInt, subterm [] TInt] TInt
    , rule "TIsZero" [subterm [] TInt] TBool
    , variable "TVar" (\index typ -> [value index, value typ])
    ]
        <> [rule "TLet" [subterm [] rhs, subterm [rhs] typ] typ | rhs <- [TInt, TBool], typ <- [TInt, TBool]]

-- | The closed well-typed terms up to the bound, from the rules.
typedLanguage :: Int -> Gen.Gen Symbol Typed
typedLanguage bound = either (error . show) id $ fromTypingRules (Typing (Nesting (fromIntegral bound)) [] [TInt, TBool] typedRules)

{- | The number of closed well-typed terms up to the bound, from a recurrence
over the environment: @count n env typ@ is the number of terms of the type in
the environment with a nesting of at most @n@.
-}
typedCount :: Int -> Integer
typedCount bound = count bound [] TInt + count bound [] TBool
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

-- | The types of the arithmetic language.
data ArithType = IntType | BoolType
    deriving stock (Eq, Ord, Show)

-- | Arithmetic with literals, a comparison, a conditional, and let-binding. A variable has no type.
data Arith = Num !Int | Flag !Bool | Plus Arith Arith | Less Arith Arith | If Arith Arith Arith | Var !Int | Let Arith Arith
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | The typing rules of 'Arith'. The type of a conditional is the type of its branches.
arithRules :: [Rule ArithType]
arithRules =
    [rule "Num" [value n] IntType | n <- [0, 1 :: Int]]
        <> [rule "Flag" [value b] BoolType | b <- [False, True]]
        <> [ rule "Plus" [subterm [] IntType, subterm [] IntType] IntType
           , rule "Less" [subterm [] IntType, subterm [] IntType] BoolType
           , variable "Var" (\index _ -> [value index])
           ]
        <> [rule "If" [subterm [] BoolType, subterm [] typ, subterm [] typ] typ | typ <- [IntType, BoolType]]
        <> [rule "Let" [subterm [] rhs, subterm [rhs] typ] typ | rhs <- [IntType, BoolType], typ <- [IntType, BoolType]]

-- | The typed arithmetic language up to the bound.
arithTyping :: Int -> Typing ArithType
arithTyping bound = Typing (Nesting (fromIntegral bound)) [] [IntType, BoolType] arithRules

-- | The closed well-typed arithmetic terms up to the bound, from the rules.
arithLanguage :: Int -> Gen.Gen Symbol Arith
arithLanguage = either (error . show) id . fromTypingRules . arithTyping

-- | The automaton of the closed well-typed arithmetic terms up to the bound.
arithAutomaton :: Int -> FTA.FTA (TypingState ArithType) Constructor Constraint
arithAutomaton = either (error . show) id . typingAutomaton @Arith . arithTyping

-- | The subterms of an arithmetic term, the term first.
subterms :: Arith -> [Arith]
subterms term =
    term
        : concatMap
            subterms
            ( case term of
                Plus left right -> [left, right]
                Less left right -> [left, right]
                If condition yes no -> [condition, yes, no]
                Let rhs body -> [rhs, body]
                _ -> []
            )

-- | Whether each conditional of the type 'IntType' in a well-typed term has two equal branches.
equalIntBranches :: [ArithType] -> Arith -> Bool
equalIntBranches env term = case term of
    If condition yes no -> (arithType env yes /= Just IntType || yes == no) && all (equalIntBranches env) [condition, yes, no]
    Plus left right -> equalIntBranches env left && equalIntBranches env right
    Less left right -> equalIntBranches env left && equalIntBranches env right
    Let rhs body -> equalIntBranches env rhs && equalIntBranches (fromMaybe (error "an ill-typed term") (arithType env rhs) : env) body
    _ -> True

-- | The type of an arithmetic term in an environment, if it has one, with the literals of the rules.
arithType :: [ArithType] -> Arith -> Maybe ArithType
arithType _ (Num n) = if n `elem` [0, 1] then Just IntType else Nothing
arithType _ (Flag _) = Just BoolType
arithType env (Plus left right) = do
    IntType <- arithType env left
    IntType <- arithType env right
    Just IntType
arithType env (Less left right) = do
    IntType <- arithType env left
    IntType <- arithType env right
    Just BoolType
arithType env (If condition yes no) = do
    BoolType <- arithType env condition
    typ <- arithType env yes
    other <- arithType env no
    if typ == other then Just typ else Nothing
arithType env (Var index)
    | index >= 0, index < length env = Just (env !! index)
    | otherwise = Nothing
arithType env (Let rhs body) = do
    rhsType <- arithType env rhs
    arithType (rhsType : env) body

-- | The nesting of an arithmetic term: the constructors with subterms on the longest path.
arithNesting :: Arith -> Int
arithNesting term = case term of
    Plus left right -> 1 + max (arithNesting left) (arithNesting right)
    Less left right -> 1 + max (arithNesting left) (arithNesting right)
    If condition yes no -> 1 + maximum (map arithNesting [condition, yes, no])
    Let rhs body -> 1 + max (arithNesting rhs) (arithNesting body)
    _ -> 0

-- | The number of closed well-typed arithmetic terms up to the bound, from a recurrence over the environment.
arithCount :: Int -> Integer
arithCount bound = count bound [] IntType + count bound [] BoolType
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

-- * Inspection

-- | The cardinality of a generator.
total :: Gen.Gen symbol a -> Integer
total generator = case Gen.cardinality generator of
    Right (Cardinality count) -> count
    Left err -> error (show err)

-- | The members of a generator, in order.
members :: (Ord a) => Gen.Gen symbol a -> [a]
members = sort . either (error . show) id . Gen.values

-- * The order of a helper type

-- | A helper type. Its constructors are declared in the reverse order of their labels.
data Letter = Z | A
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | A language with one constructor, whose field has the helper type.
newtype Lettered = Lit Letter
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

-- | A non-regular type: each level nests its element type in a list.
data Nested a = Here a | Deeper (Nested [a])
    deriving stock (Eq, Ord, Show, Generic)

instance (HasFTA a) => HasFTA (Nested a)

-- | A language with a field of the non-regular type, which no rule uses.
data Holding = Plain | Other | Holder (Nested Int)
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

spec :: Spec
spec = describe "Data.CFTA.Gen.Typing" $ do
    describe "the language of the binders spike" $ do
        it "gives the members of the hand-written automaton up to the bounds 2 and 3" $ do
            members (typedLanguage 2) `shouldBe` members (handWritten 2)
            members (typedLanguage 3) `shouldBe` members (handWritten 3)
            length (members (typedLanguage 2)) `shouldBe` 222
        it "counts the terms of the recurrence up to the bound 6" $
            map (total . typedLanguage) [0 .. 6] `shouldBe` map typedCount [0 .. 6]
        it "gives each value the rank of its term" $ do
            let generator = typedLanguage 2
            mapM (Gen.rankOfValue generator) (either (error . show) id (Gen.values generator))
                `shouldBe` Right (map Rank [0 .. total generator - 1])
    describe "typed arithmetic" $ do
        it "counts the terms of the recurrence up to the bound 6" $
            map (total . arithLanguage) [0 .. 6] `shouldBe` map arithCount [0 .. 6]
        it "gives distinct well-typed terms of a nesting up to the bound 2, as many as the recurrence" $ do
            let listed = either (error . show) id (Gen.values (arithLanguage 2))
            filter (isNothing . arithType []) listed `shouldBe` []
            filter ((> 2) . arithNesting) listed `shouldBe` []
            length (nubOrd listed) `shouldBe` length listed
            fromIntegral (length listed) `shouldBe` arithCount 2
        it "decodes sampled ranks to well-typed terms up to the bound 3, and ranks them back" $ do
            let generator = arithLanguage 3
                count = total generator
                ranks = [Rank (index * (count - 1) `div` 199) | index <- [0 .. 199]]
                decoded = either (error . show) id (mapM (Gen.unrank generator) ranks)
            filter (isNothing . arithType []) decoded `shouldBe` []
            filter ((> 3) . arithNesting) decoded `shouldBe` []
            mapM (Gen.rankOfValue generator) decoded `shouldBe` Right ranks
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
                product' = either (error . show) id $ FTA.intersectWith same conjoinConstraints (arithAutomaton 2) (datatypeFTA annotated)
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
    describe "the rules" $ do
        it "names only constructors of the datatype" $
            either
                Just
                (const Nothing)
                (fromTypingRules @Arith (Typing (Nesting 1) [] [IntType] [rule "Num" [value (0 :: Int)] IntType, rule "Mul" [] IntType]))
                `shouldBe` Just (UnknownConstructors ["Mul"] ["Num", "Flag", "Plus", "Less", "If", "Var", "Let"])
        it "report inputs and a bound on the binders as not implemented" $ do
            let failure typing = either Just (const Nothing) (fromTypingRules @Arith typing)
            failure (Typing (Nesting 1) [IntType] [IntType] arithRules) `shouldBe` Just (NotImplemented "inputs")
            failure (Typing (Binders 1) [] [IntType] arithRules) `shouldBe` Just (NotImplemented "a bound on the binders")
        it "fit the fields of their constructor" $ do
            let mismatch given = either Just (const Nothing) (fromTypingRules @Arith (Typing (Nesting 1) [] [IntType] given))
            mismatch [rule "Plus" [subterm [] IntType] IntType] `shouldBe` Just (FieldMismatch "Plus")
            mismatch [rule "Num" [subterm [] IntType] IntType] `shouldBe` Just (FieldMismatch "Num")
            mismatch [rule "Num" [value True] IntType] `shouldBe` Just (FieldMismatch "Num")
            mismatch [rule "Let" [value (Var 99), subterm [IntType] IntType] IntType] `shouldBe` Just (FieldMismatch "Let")
            mismatch [rule "Let" [value (Plus (Num 0) (Num 0)), subterm [IntType] IntType] IntType]
                `shouldBe` Just (FieldMismatch "Let")
            mismatch [rule "Let" [value (0 :: Int), subterm [IntType] IntType] IntType] `shouldBe` Just (FieldMismatch "Let")
            mismatch
                [ rule "Num" [value (0 :: Int)] IntType
                , rule "Let" [subterm [] IntType, subterm [IntType] IntType] IntType
                , variable "Var" (\_ _ -> [value False])
                ]
                `shouldBe` Just (FieldMismatch "Var")
    describe "the order of the values" $ do
        it "orders the constructors of a helper type in declaration order, as fromDatatype does" $ do
            let typed =
                    either (error . show) id $
                        fromTypingRules @Lettered (Typing (Nesting 0) [] [()] [rule "Lit" [value A] (), rule "Lit" [value Z] ()])
                derived = Gen.fromDatatype $ either (error . show) id $ deriveFTA @Lettered
            Gen.values derived `shouldBe` Right [Lit Z, Lit A]
            Gen.values typed `shouldBe` Right [Lit Z, Lit A]
        it "reads only the types of the rules, so a non-regular field that no rule uses does not stop it" $
            Gen.values
                ( either (error . show) id $
                    fromTypingRules @Holding (Typing (Nesting 0) [] [()] [rule "Other" [] (), rule "Plain" [] ()])
                )
                `shouldBe` Right [Plain, Other]
