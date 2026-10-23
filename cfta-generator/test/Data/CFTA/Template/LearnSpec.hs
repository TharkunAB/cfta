{-# LANGUAGE OverloadedStrings #-}

-- | Learned exclusions on arithmetic expressions over @x@, @0@, and @1@.
module Data.CFTA.Template.LearnSpec (spec) where

import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Sized (Sized, rankOfSize, sized, termsOfSize)
import Data.CFTA.Template (Template (..), excludeAnywhereFTA, excludeFTA, matchesNone, matchesNowhere, matchesTemplate)
import Data.CFTA.Template.Learn
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | Expressions: the leaves @x@, @0@, and @1@, and the operators @+@, @*@, @-@, and @/@.
expressions :: FTA.FTA Text Text Constraint
expressions =
    either (error . show) id $
        FTA.mkFTA "e" [("e", [leaf "x", leaf "0", leaf "1", binary "+", binary "*", binary "-", binary "/"])]
  where
    leaf symbol = FTA.Transition symbol [] noConstraint
    binary symbol = FTA.Transition symbol ["e", "e"] noConstraint

x, zero, one :: Term Text
x = Term.Node "x" []
zero = Term.Node "0" []
one = Term.Node "1" []

-- | An operator applied to two expressions.
operator :: Text -> Term Text -> Term Text -> Term Text
operator symbol left right = Term.Node symbol [left, right]

-- | The template that matches one term only.
exactly :: Term Text -> Template Text
exactly (Term.Node symbol children) = TemplateNode symbol (map exactly children)

-- | The size classes of an automaton without guards.
classesOf :: (Ord state) => FTA.FTA state Text Constraint -> Sized Text
classesOf = either (error . show) id . sized

-- | Each term of the expressions with at most the given number of nodes.
expressionsUpTo :: Size -> [Term Text]
expressionsUpTo bound = concatMap (termsOfSize (classesOf expressions)) [1 .. bound]

-- | Whether a learned template list removes a term with a placement.
removedBy :: Placement -> [Template Text] -> Term Text -> Bool
removedBy AtRoot templates term = not (matchesNone templates term)
removedBy Anywhere templates term = not (matchesNowhere templates term)

-- | The expressions that a placement keeps, as an automaton.
keptBy :: Placement -> [Template Text] -> Sized Text
keptBy AtRoot templates = classesOf (excludeFTA templates expressions)
keptBy Anywhere templates = classesOf (excludeAnywhereFTA templates expressions)

{- | Check the learned exclusions of one example: each rejected term without a
conflict is removed, each accepted term is kept, both in the term check and
in the excluded language, and the price agrees with brute force up to size 5.
-}
checkLearned :: Placement -> [Term Text] -> [Term Text] -> IO (Learned Text)
checkLearned placement rejected accepted = do
    let learned = learnExclusions placement rejected accepted
        templates = map exclusionTemplate (learnedExclusions learned)
        separable = filter (`notElem` map conflictRejected (learnedConflicts learned)) rejected
        kept = keptBy placement templates
        bound = 5
        everyTerm = expressionsUpTo bound
        removed = filter (removedBy placement templates) everyTerm
    separable `shouldSatisfy` all (removedBy placement templates)
    accepted `shouldSatisfy` not . any (removedBy placement templates)
    separable `shouldSatisfy` all (isNothing . rankOfSize kept)
    accepted `shouldSatisfy` all (isJust . rankOfSize kept)
    exclusionPrice placement bound rejected templates expressions
        `shouldBe` Right
            ( Price
                (toInteger (length everyTerm))
                (toInteger (length everyTerm - length removed))
                (toInteger (length (filter (`elem` removed) separable)))
            )
    pure learned

spec :: Spec
spec = describe "Data.CFTA.Template.Learn" $ do
    let divide = operator "/"
        minus = operator "-"
        plus = operator "+"
        divisionByZero = TemplateNode "/" [Hole, TemplateNode "0" []]

    describe "generalize" $ do
        it "keeps the shared symbols and puts holes where the terms differ" $
            generalize (divide x zero :| [divide (plus x one) zero]) `shouldBe` divisionByZero

        it "gives AnyNode for different symbols of one arity" $ do
            generalize (plus x zero :| [operator "*" x zero]) `shouldBe` AnyNode [exactly x, exactly zero]
            generalize (x :| [zero]) `shouldBe` AnyNode []

        it "gives Hole for different arities" $
            generalize (x :| [plus x x]) `shouldBe` Hole

        it "forgets that two positions hold the same subterm" $
            generalize (minus x x :| [minus one one]) `shouldBe` TemplateNode "-" [AnyNode [], AnyNode []]

        it "gives a template that each term matches" $ do
            let small = expressionsUpTo 3
            [ (left, right) | left <- small, right <- small, not (all (matchesTemplate (generalize (left :| [right]))) [left, right])
              ]
                `shouldBe` []

    describe "learnExclusions" $ do
        it "learns one template for the divisions by zero" $ do
            learned <-
                checkLearned
                    AtRoot
                    [divide x zero, divide one zero, divide (plus x one) zero]
                    [divide x one, divide zero x, plus x zero]
            map exclusionTemplate (learnedExclusions learned) `shouldBe` [divisionByZero]
            learnedConflicts learned `shouldBe` []

        it "needs one template for each rejected term when a shared subterm separates them" $ do
            -- With named variables, v - v would remove both and keep x - 1.
            learned <-
                checkLearned AtRoot [minus x x, minus one one, divide x zero, divide one zero] [minus x one, minus one x, divide zero x]
            map exclusionTemplate (learnedExclusions learned)
                `shouldBe` [exactly (minus one one), exactly (minus x x), TemplateNode "/" [AnyNode [], exactly zero]]

        it "reports a rejected term that an accepted term is equal to" $ do
            learned <- checkLearned AtRoot [divide x zero, plus x x] [plus x x, divide zero x]
            learnedConflicts learned `shouldBe` [Conflict (plus x x) (plus x x)]
            map exclusionTemplate (learnedExclusions learned) `shouldBe` [exactly (divide x zero)]

        it "learns a template for each subterm position" $ do
            learned <- checkLearned Anywhere [divide x zero, divide one zero] [plus (divide x one) zero, divide zero x]
            map exclusionTemplate (learnedExclusions learned) `shouldBe` [TemplateNode "/" [AnyNode [], TemplateNode "0" []]]

        it "reports a rejected term that an accepted term contains" $ do
            learned <- checkLearned Anywhere [divide x zero, divide one zero] [plus (divide x zero) one]
            learnedConflicts learned `shouldBe` [Conflict (divide x zero) (plus (divide x zero) one)]
            map exclusionTemplate (learnedExclusions learned) `shouldBe` [exactly (divide one zero)]

    describe "exclusionPrice" $
        it "counts the terms that a template removes at the root and anywhere" $ do
            let rejected = [divide x zero, divide one zero, divide (plus x one) zero]
            -- Up to size 5: 3 divisions of a leaf by zero, and 36 of a size-3 term.
            exclusionPrice AtRoot 5 rejected [divisionByZero] expressions `shouldBe` Right (Price 903 864 3)
            -- Anywhere also removes 69 terms of size 5 with a division by zero below the root.
            exclusionPrice Anywhere 5 rejected [divisionByZero] expressions `shouldBe` Right (Price 903 795 3)
