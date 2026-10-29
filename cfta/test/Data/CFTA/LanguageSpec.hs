{-# LANGUAGE OverloadedStrings #-}

-- | Language updates: source edits and named exclusions, checked on the compiled terms.
module Data.CFTA.LanguageSpec (spec) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Language (Language, UpdateError (..))
import qualified Data.CFTA.Language as Language
import qualified Data.CFTA.Language.Source as Source
import Data.CFTA.Symbol (Symbol, symbolText)
import Data.CFTA.Template (Exclusion (Anywhere), Template (Hole, TemplateNode))
import Data.CFTA.Term (Term (Node))

-- | The states of the test language.
data State = Atom | Expr
    deriving (Eq, Ord, Show)

spec :: Spec
spec = describe "language updates" $ do
    it "exclude a whole term only at the root" $
        terms (changed $ Language.without "rule" $ Language.wholeTerm $ pair zero zero)
            `shouldBe` Set.fromList [pair zero one, pair one zero, pair one one]

    it "exclude every term that contains a subterm" $
        terms (changed $ Language.without "rule" $ Language.subterm zero)
            `shouldBe` Set.fromList [pair one one]

    it "apply a root exclusion and a subterm exclusion together" $
        terms
            ( changed $
                Language.without "zeros" (Language.wholeTerm $ pair zero zero)
                    <> Language.without "one-first" (Anywhere $ TemplateNode "pair" [TemplateNode "one" [], Hole])
            )
            `shouldBe` Set.fromList [pair zero one]

    it "restore the terms of a named exclusion" $ do
        let excluded =
                changed $
                    Language.without "rule" (Language.subterm zero) <> Language.without "other" (Language.wholeTerm $ pair one one)
        terms (update excluded $ Language.restore "rule") `shouldBe` Set.delete (pair one one) (terms original)
        Language.source excluded `shouldBe` Language.source original

    it "apply source edits and exclusions in one update" $
        terms (changed $ Language.define (Language.at Atom "two") "two" [] <> Language.without "rule" (Language.subterm zero))
            `shouldBe` Set.fromList [pair x y | x <- [one, two], y <- [one, two]]

    it "report a missing exclusion and an invalid source edit" $ do
        Language.update original (Language.restore "absent") `shouldBe` Left (MissingExclusion "absent")
        Language.update original (Language.remove $ Language.at Atom "absent")
            `shouldBe` Left (InvalidSource $ Source.MissingProduction Atom "absent")
  where
    changed = update original
    update before = either (error . Language.explainUpdateError) id . Language.update before
    pair left right = Node "pair" [left, right]
    zero = Node "zero" []
    one = Node "one" []
    two = Node "two" []

-- | Pairs of two atoms, with no facts, so that the plain terms are the terms.
original :: Language State
original =
    Language.fromDocument
        $ either (error . Source.explainDocumentError) id
        $ Source.mkDocument
            Expr
            [ (Expr, [production "pair" [Atom, Atom]])
            , (Atom, [production "zero" [], production "one" []])
            ]
  where
    production symbol children = FTA.Transition symbol children $ Source.Annotation (Source.ProductionName $ symbolText symbol) Map.empty

-- | The terms of the compiled language.
terms :: Language State -> Set.Set (Term Symbol)
terms = Set.fromList . FTA.terms . Language.compileGraph
