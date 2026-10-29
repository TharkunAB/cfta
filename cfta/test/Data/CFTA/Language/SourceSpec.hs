{-# LANGUAGE OverloadedStrings #-}

-- | Source documents: validation, checked patches, named facts, and compilation.
module Data.CFTA.Language.SourceSpec (spec) where

import Control.Monad (void)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint,
    Guard (Bottom),
    conjoinConstraints,
    equalityConstraint,
    noConstraint,
    semanticConstraint,
 )
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Language.Source (Annotation (..), DocumentError (..), Edit (..))
import qualified Data.CFTA.Language.Source as Source
import Data.CFTA.Path (path)
import Data.CFTA.Symbol (Symbol)

-- | The states of the test documents.
data State = Atom | Expr | Extra
    deriving (Eq, Ord, Show)

spec :: Spec
spec = describe "source documents" $ do
    it "reject a duplicate state row" $
        Source.mkDocument Expr (rows <> [(Atom, [])]) `shouldBe` Left (DuplicateState Atom)

    it "reject a duplicate production name in a row" $
        Source.mkDocument Atom [(Atom, [production "zero" [] "z", production "one" [] "z"])]
            `shouldBe` Left (DuplicateProduction Atom "z")

    it "reject a patch prepared on another document" $ do
        let other = edited [DeleteProduction Atom "one"]
        Source.applyPatch (Source.patch other [DeleteProduction Atom "zero"]) document
            `shouldBe` Left StalePatch

    it "keep the facts of a production that define changes" $
        facts (edited [DefineProduction Expr "pair" "tuple" [Atom, Atom]]) Expr
            `shouldBe` [("tuple", Map.keys pairFacts)]

    it "append a production with no facts for a new name" $
        facts (edited [DefineProduction Expr "wrap" "wrap" [Expr]]) Expr
            `shouldBe` [("pair", Map.keys pairFacts), ("wrap", [])]

    it "replace, add, and remove single facts" $ do
        let changed =
                edited [SetFact Expr "pair" "same" noConstraint, SetFact Expr "pair" "new" disabled, RemoveFact Expr "pair" "disabled"]
        Map.toList . annotationFacts <$> annotations changed Expr
            `shouldBe` [[("new", disabled), ("same", noConstraint)]]

    it "report a missing fact, production, and state" $ do
        let attempt edit = Source.applyPatch (Source.patch document [edit]) document
        attempt (RemoveFact Expr "pair" "absent") `shouldBe` Left (MissingFact Expr "pair" "absent")
        attempt (DeleteProduction Expr "absent") `shouldBe` Left (MissingProduction Expr "absent")
        attempt (DeleteRow Extra) `shouldBe` Left (MissingState Extra)

    it "check references after the complete batch" $ do
        let forward = [PutProduction Expr $ production "extra" [Extra] "extra", PutRow Extra [production "leaf" [] "leaf"]]
        void (Source.applyPatch (Source.patch document forward) document) `shouldBe` Right ()
        Source.applyPatch (Source.patch document $ take 1 forward) document
            `shouldBe` Left (InvalidGraph $ FTA.DanglingState Extra)

    it "set the initial state, which must have a row after the complete batch" $ do
        let start = FTA.initialState . Source.sourceGraph
        start (edited [SetStart Atom]) `shouldBe` Atom
        start (edited [SetStart Atom, SetStart Extra, PutRow Extra [production "leaf" [] "leaf"], DeleteRow Expr])
            `shouldBe` Extra
        Source.applyEdits [SetStart Extra] document `shouldBe` Left (InvalidGraph $ FTA.MissingInitialState Extra)
        Source.applyEdits [DeleteRow Expr] document `shouldBe` Left (InvalidGraph $ FTA.MissingInitialState Expr)

    it "conjoin the facts of each production" $
        map FTA.transitionConstraint (rowOf Expr $ Source.compileGraph document)
            `shouldBe` [foldl1 conjoinConstraints $ Map.elems pairFacts]

    it "compile an imported graph to the same graph" $ do
        let graph = Source.compileGraph document
        Source.compileGraph <$> Source.fromGraph graph `shouldBe` Right graph
  where
    edited edits = either (error . Source.explainDocumentError) id $ Source.applyPatch (Source.patch document edits) document
    facts changed state =
        [ (FTA.transitionSymbol transition, Map.keys $ annotationFacts $ FTA.transitionConstraint transition)
        | transition <- rowOf state $ Source.sourceGraph changed
        ]
    annotations changed state = map FTA.transitionConstraint $ rowOf state $ Source.sourceGraph changed

-- | A pair of atoms whose production has three named facts.
document :: Source.Document State
document = either (error . Source.explainDocumentError) id $ Source.mkDocument Expr rows

-- | The rows of the test document.
rows :: [(State, [FTA.Transition State Symbol Annotation])]
rows =
    [ (Expr, [FTA.Transition "pair" [Atom, Atom] $ Annotation "pair" pairFacts])
    , (Atom, [production "zero" [] "zero", production "one" [] "one"])
    ]

-- | The facts of the pair production.
pairFacts :: Map.Map Text Constraint
pairFacts =
    Map.fromList
        [ ("same", equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
        , ("disabled", disabled)
        ]

-- | A fact that no term satisfies.
disabled :: Constraint
disabled = semanticConstraint Bottom

-- | A production with no facts.
production :: Symbol -> [State] -> Text -> FTA.Transition State Symbol Annotation
production symbol children name = FTA.Transition symbol children $ Annotation name Map.empty

-- | The transitions of one state.
rowOf :: (Ord state) => state -> FTA.FTA state Symbol constraint -> [FTA.Transition state Symbol constraint]
rowOf state = Map.findWithDefault [] state . FTA.transitionTable
