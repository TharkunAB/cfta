{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

{- | Refinement generators over the automaton of a typed language: the
measures and the contracts of an invariant hold on the well-typed terms.
-}
module Data.CFTA.Gen.Refinement.TypedLanguageSpec (spec) where

import Data.List (sort)
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Refinement.Derive
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.TypedArithmeticLanguage
import Data.CFTA.Gen.Typing (
    Bound (..),
    Rule,
    Typing (Typing),
    TypingError (..),
    drawn,
    fromTypingRules,
    rule,
    typingAutomaton,
    typingLTA,
    typingLTAFrom,
    value,
 )
import Data.CFTA.Generic (Constructor (..), HasFTA (..))
import Data.CFTA.Index (Cardinality (..))
import Data.CFTA.Path (path)
import qualified Data.CFTA.Term as Term

{- | The sum of the literals of a term: a literal is its value, a variable is
0, and a let is its body. A sum adds at most 1.
-}
smallSums :: Invariant ArithNode Single
smallSums = Measured sumOf small
  where
    sumOf (NumNode n) = n
    sumOf (PlusNode left right) = left + right
    sumOf (LetNode _ body) = body
    sumOf _ = 0
    small (PlusNode left right) = left + right .<= 1
    small _ = true

-- | Two measures: the sum, as for 'smallSums', and the number of literals.
data Sums e = Sums {total :: e, literals :: e}
    deriving stock (Eq, Show, Generic)
    deriving anyclass (MeasureRecord)

-- | One node of a typed arithmetic term, for the named measures.
data ArithByNode e
    = NumBy e
    | FlagBy e
    | PlusBy (Sums e) (Sums e)
    | LessBy (Sums e) (Sums e)
    | IfBy (Sums e) (Sums e) (Sums e)
    | VarBy e
    | LetBy (Sums e) (Sums e)
    | ArgBy e
    deriving stock (Generic)
    deriving anyclass (NodeView)

-- | A sum adds at most 1, and the branches of a conditional have at most two literals.
fewLiterals :: Invariant ArithByNode Sums
fewLiterals = MeasuredBy measures holdsAt
  where
    measures (NumBy n) = Sums n 1
    measures (PlusBy left right) = Sums (total left + total right) (literals left + literals right)
    measures (LessBy left right) = Sums 0 (literals left + literals right)
    measures (IfBy condition yes no) = Sums 0 (literals condition + literals yes + literals no)
    measures (LetBy rhs body) = Sums (total body) (literals rhs + literals body)
    measures _ = Sums 0 0
    holdsAt (PlusBy left right) = total left + total right .<= 1
    holdsAt (IfBy _ yes no) = literals yes + literals no .<= 2
    holdsAt _ = true

-- | The integers of the atomic fields: the literals and the indices.
atoms :: Atoms
atoms = atom @Int (LTAGen.elements [0, 1])

-- | The members of a refinement generator, compiled, in order.
compiledMembers :: (Ord a) => Either DeriveLTAError (LTAGen.LTAGen a) -> IO [a]
compiledMembers derived = do
    generator <- either (fail . show) LTAGen.compile derived
    either (fail . show) (pure . sort) (LTAGen.values generator)

-- | The members of a typed language, in order.
typedMembers :: (Ord a) => Gen.Gen symbol a -> [a]
typedMembers = sort . either (error . show) id . Gen.values

-- | The constructor at the root of a value.
constructorOf :: (HasFTA v) => v -> Constructor
constructorOf = Term.rootLabel . encodeTerm

-- | The typed arithmetic whose numbers are drawn from a generator, in place of one rule for each number.
drawnArith :: LTAGen.LTAGen Int -> Int -> Typing ArithNode ArithType
drawnArith numbers bound = Typing (Nesting (fromIntegral bound)) [] [IntType, BoolType] (drawnNumbers numbers <> arithOperatorRules)

-- | The rule of the numbers, drawn from the generator.
drawnNumbers :: LTAGen.LTAGen Int -> [Rule ArithNode ArithType]
drawnNumbers numbers = [rule (NumNode (drawn numbers)) IntType]

-- | The integers from 0 to the bound, as a refinement generator without a list.
upTo :: Int -> LTAGen.LTAGen Int
upTo top = LTAGen.every `LTAGen.satisfying` (\v -> 0 .<= v .&& v .<= fromIntegral top)

{- | The number of closed well-typed arithmetic terms up to the bound with
the count of numbers, from the recurrence of the typing tests.
-}
arithCountWith :: Integer -> Int -> Integer
arithCountWith numbers bound = count bound [] IntType + count bound [] BoolType
  where
    leaves env typ = (if typ == IntType then numbers else 2) + fromIntegral (length (filter (== typ) env))
    count :: Int -> [ArithType] -> ArithType -> Integer
    count 0 env typ = leaves env typ
    count n env typ =
        leaves env typ
            + below env IntType * below env IntType
            + below env BoolType * below env typ * below env typ
            + sum [below env rhs * below (rhs : env) typ | rhs <- [IntType, BoolType]]
      where
        below = count (n - 1)

-- | The members of the refinement generator of a typed language, compiled, in order.
typedLTAMembers :: (Ord a) => Either TypingError (LTAGen.LTAGen a) -> IO [a]
typedLTAMembers typed = do
    generator <- either (fail . show) LTAGen.compile typed
    either (fail . show) (pure . sort) (LTAGen.values generator)

spec :: Spec
spec = describe "refinement generators over a typed language" $ do
    it "draw a field from every with a condition, and count the language without listing the numbers" $ do
        compiled <- either (fail . show) LTAGen.compile (typingLTA @Arith (drawnArith (upTo 1000000) 2) atoms)
        LTAGen.cardinality compiled `shouldBe` Right (Cardinality (arithCountWith 1000001 2))
    it "draw a field from a finite generator as the same rules with fixed values do" $
        typedLTAMembers (typingLTA @Arith (drawnArith (LTAGen.elements [0, 1]) 2) atoms)
            >>= (`shouldBe` typedMembers (arithLanguage 2))
    it "keep the terms with drawn fields on which an invariant holds" $ do
        typedLTAMembers (typingLTAFrom @Arith (drawnArith (LTAGen.elements [0, 1]) 2) atoms smallSums)
            >>= (`shouldBe` filter (holds atoms smallSums) (typedMembers (arithLanguage 2)))
        let fixed =
                typingAutomaton @Arith
                    ( Typing
                        (Nesting 2)
                        []
                        [IntType, BoolType]
                        ([rule (NumNode (value n)) IntType | n <- [0 .. 3 :: Int]] <> arithOperatorRules)
                    )
        fromFixed <-
            either (fail . show) pure fixed >>= \automaton ->
                either (fail . show) LTAGen.compile (deriveLTAOnFrom @Arith automaton (atom @Int (LTAGen.elements [0 .. 3])) smallSums)
        fromDrawn <- either (fail . show) LTAGen.compile (typingLTAFrom @Arith (drawnArith (upTo 3) 2) atoms smallSums)
        LTAGen.cardinality fromDrawn `shouldBe` LTAGen.cardinality fromFixed
    it "report a drawn field to the plain builder" $
        either Just (const Nothing) (fromTypingRules @Arith (drawnArith (upTo 3) 1)) `shouldBe` Just (DrawnField "Num")
    it "keep the well-typed terms on which a measured invariant holds, at the bound 2" $
        compiledMembers (deriveLTAOnFrom @Arith (arithAutomaton 2) atoms smallSums)
            >>= (`shouldBe` filter (holds atoms smallSums) (typedMembers (arithLanguage 2)))
    it "keep the well-typed terms on which an invariant with named measures holds, at the bound 2" $
        compiledMembers (deriveLTAOnFrom @Arith (arithAutomaton 2) atoms fewLiterals)
            >>= (`shouldBe` filter (holds atoms fewLiterals) (typedMembers (arithLanguage 2)))
    it "report a cyclic automaton" $ do
        let cyclic =
                either (error . show) id $
                    FTA.mkFTA
                        (0 :: Int)
                        [
                            ( 0
                            ,
                                [ FTA.Transition (constructorOf (Plus (Num 0) (Num 0))) [0, 0] noConstraint
                                , FTA.Transition (constructorOf (Num 0)) [1] noConstraint
                                ]
                            )
                        , (1, [FTA.Transition (constructorOf (0 :: Int)) [] noConstraint])
                        ]
        either Just (const Nothing) (deriveLTAOnFrom @Arith cyclic atoms smallSums) `shouldBe` Just CyclicAutomaton
    it "report a transition with a constraint" $ do
        let equalBranches = equalityConstraint (mkEqConstraints [[path [1], path [2]]])
            annotation _ transition
                | constructorName (FTA.transitionSymbol transition) == "If" = equalBranches
                | otherwise = noConstraint
        either Just (const Nothing) (deriveLTAOnFrom @Arith (FTA.annotate annotation (arithAutomaton 1)) atoms smallSums)
            `shouldBe` Just (ConstrainedTransition "If")
