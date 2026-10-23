{-# LANGUAGE OverloadedStrings #-}

-- | Templates with a repeated name on arithmetic expressions, and the routes that count them.
module Data.CFTA.Template.NamedSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (void)
import Data.List (sort)
import Test.Hspec (Spec, anyErrorCall, describe, it, shouldBe, shouldThrow)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (Cardinality (..), Rank (..), Size (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Sized (Sized, SizedError (ResidualGuard), countOfSize, sized, sizedUpTo)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..), excludeFTA, matchesNone, matchesNowhere, matchesTemplate)
import Data.CFTA.Template.Learn (Placement (..), Price (..), exclusionPriceUpTo, generalize, priceExtra)
import Data.CFTA.Template.LearnSpec (expressions, expressionsUpTo, one, operator, syntactic, x, zero)
import Data.CFTA.Template.Named (excludeNamedAnywhereFTA, excludeNamedFTA, restrictNamedFTA)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import Data.List.NonEmpty (NonEmpty (..))

-- | The number of terms of the size classes from 1 to a bound.
total :: Sized Symbol -> Size -> Integer
total classes bound = sum [count | size <- [1 .. bound], let Cardinality count = countOfSize classes size]

-- | The template that matches one term only.
exactly :: Term Symbol -> Template Symbol
exactly (Term.Node symbol children) = TemplateNode symbol (map exactly children)

spec :: Spec
spec = describe "Data.CFTA.Template.Named" $ do
    let minus = operator "-"
        plus = operator "+"
        same = TemplateNode "-" [NamedHole "v", NamedHole "v"]
        twoNames = TemplateNode "-" [NamedHole "a", NamedHole "b"]
        bound = 7
        everyTerm = expressionsUpTo bound
        count = toInteger . length

    describe "matchesTemplate" $
        it "requires equal subterms at the holes of one name" $ do
            map (matchesTemplate same) [minus x x, minus x one, minus (plus x one) (plus x one)] `shouldBe` [True, False, True]
            matchesTemplate twoNames (minus x one) `shouldBe` True

    describe "the linear operations" $ do
        it "read a name that occurs once as a hole" $
            excludeFTA [twoNames] expressions `shouldBe` excludeFTA [TemplateNode "-" [Hole, Hole]] expressions

        it "reject a repeated name" $
            evaluate (length (show (excludeFTA [same] expressions))) `shouldThrow` anyErrorCall

    describe "restrictNamedFTA" $
        it "keeps the terms with equal subterms, and Data.CFTA.Sized counts them" $ do
            let classes = either (error . show) id (sized (restrictNamedFTA same expressions))
            -- 3 of size 3 and 36 of size 7.
            total classes bound `shouldBe` 39
            total classes bound `shouldBe` count (filter (matchesTemplate same) everyTerm)

    describe "excludeNamedFTA and excludeNamedAnywhereFTA" $ do
        it "give a guard that sized rejects" $ do
            void (sized (excludeNamedFTA [same] expressions)) `shouldBe` Left ResidualGuard
            void (sized (excludeNamedAnywhereFTA [same] expressions)) `shouldBe` Left ResidualGuard

        it "count exactly with sizedUpTo" $ do
            atRoot <- either (error . show) id <$> sizedUpTo syntactic bound (excludeNamedFTA [same] expressions)
            anywhere <- either (error . show) id <$> sizedUpTo syntactic bound (excludeNamedAnywhereFTA [same] expressions)
            total atRoot bound `shouldBe` count (filter (matchesNone [same]) everyTerm)
            total anywhere bound `shouldBe` count (filter (matchesNowhere [same]) everyTerm)
            (total atRoot bound, total anywhere bound) `shouldBe` (26784, 24159)

        it "count and rank exactly with the equality generator up to a depth" $ do
            let depth = 2
                language = Gen.fromAutomatonUpToDepth depth (fromFTA expressions)
                atRoot = Gen.fromAutomatonUpToDepth depth (fromFTA (excludeNamedFTA [same] expressions))
                anywhere = Gen.fromAutomatonUpToDepth depth (fromFTA (excludeNamedAnywhereFTA [same] expressions))
            fmap sort (Gen.values atRoot) `shouldBe` fmap (sort . filter (matchesNone [same])) (Gen.values language)
            fmap sort (Gen.values anywhere) `shouldBe` fmap (sort . filter (matchesNowhere [same])) (Gen.values language)
            (Gen.cardinality language, Gen.cardinality atRoot, Gen.cardinality anywhere)
                `shouldBe` (Right 6087, Right 6048, Right 5151)
            [Gen.unrank atRoot rank >>= Gen.rankOfTerm atRoot | rank <- map Rank [0, 97 .. 6047]]
                `shouldBe` [Right rank | rank <- map Rank [0, 97 .. 6047]]

        it "cannot be counted by size with the equality generator" $
            Gen.cardinality (Gen.upToSize bound (Gen.fromAutomaton (fromFTA (excludeNamedFTA [same] expressions))))
                `shouldBe` Left Gen.CannotCountConstrainedEdges

    describe "a bounded exclusion of the ground instances" $
        it "is exact up to the bound and keeps larger instances" $ do
            let instances = [exactly term | term <- everyTerm, matchesTemplate same term]
                bounded = excludeFTA instances expressions
                classes = either (error . show) id (sized bounded)
                large = minus (plus (plus x x) x) (plus (plus x x) x)
            length instances `shouldBe` 39
            total classes bound `shouldBe` count (filter (matchesNone [same]) everyTerm)
            (FTA.accepts bounded large, matchesTemplate same large) `shouldBe` (True, True)

    describe "a learned v0 - v0" $
        it "has the price that brute force counts" $ do
            let rejected = [minus x x, minus one one]
                learned = generalize (minus x x :| [minus one one])
            learned `shouldBe` TemplateNode "-" [NamedHole "v0", NamedHole "v0"]
            atRoot <- exclusionPriceUpTo AtRoot bound rejected [learned] expressions
            anywhere <- exclusionPriceUpTo Anywhere bound rejected [learned] expressions
            atRoot `shouldBe` Right (Price 26823 26784 2)
            anywhere `shouldBe` Right (Price 26823 24159 2)
            (priceExtra <$> atRoot, priceExtra <$> anywhere) `shouldBe` (Right 37, Right 2662)
            -- The anonymous generalization removes every subtraction instead.
            map (matchesTemplate (TemplateNode "-" [AnyNode [], AnyNode []])) [minus x one, minus zero one] `shouldBe` [True, True]
