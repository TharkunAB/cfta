{-# LANGUAGE OverloadedStrings #-}

-- | Source documents: validation, checked patches, named facts, and compilation.
module Data.CFTA.DocumentSpec (spec) where

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
import Data.CFTA.Document (Annotation (..), DocumentError (..), Edit (..))
import qualified Data.CFTA.Document as Document
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import Data.CFTA.Symbol (Symbol)

-- | The states of the test documents.
data State = Atom | Expr | Extra
    deriving (Eq, Ord, Show)

spec :: Spec
spec = describe "source documents" $ do
    it "reject a duplicate state row" $
        Document.mkDocument Expr (rows <> [(Atom, [])]) `shouldBe` Left (DuplicateState Atom)

    it "reject a duplicate production name in a row" $
        Document.mkDocument Atom [(Atom, [production "zero" [] "z", production "one" [] "z"])]
            `shouldBe` Left (DuplicateProduction Atom "z")

    it "reject a patch prepared on another document" $ do
        let other = edited [DeleteProduction Atom "one"]
        Document.applyPatch (Document.patch other [DeleteProduction Atom "zero"]) document
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
        let attempt edit = Document.applyPatch (Document.patch document [edit]) document
        attempt (RemoveFact Expr "pair" "absent") `shouldBe` Left (MissingFact Expr "pair" "absent")
        attempt (DeleteProduction Expr "absent") `shouldBe` Left (MissingProduction Expr "absent")
        attempt (DeleteRow Extra) `shouldBe` Left (MissingState Extra)

    it "check references after the complete batch" $ do
        let forward = [PutProduction Expr $ production "extra" [Extra] "extra", PutRow Extra [production "leaf" [] "leaf"]]
        void (Document.applyPatch (Document.patch document forward) document) `shouldBe` Right ()
        Document.applyPatch (Document.patch document $ take 1 forward) document
            `shouldBe` Left (InvalidGraph $ FTA.DanglingState Extra)

    it "set the initial state, which must have a row after the complete batch" $ do
        let start = FTA.initialState . Document.sourceGraph
        start (edited [SetStart Atom]) `shouldBe` Atom
        start (edited [SetStart Atom, SetStart Extra, PutRow Extra [production "leaf" [] "leaf"], DeleteRow Expr])
            `shouldBe` Extra
        Document.applyEdits [SetStart Extra] document `shouldBe` Left (InvalidGraph $ FTA.MissingInitialState Extra)
        Document.applyEdits [DeleteRow Expr] document `shouldBe` Left (InvalidGraph $ FTA.MissingInitialState Expr)

    it "conjoin the facts of each production" $
        map FTA.transitionConstraint (rowOf Expr $ Document.compileGraph document)
            `shouldBe` [foldl1 conjoinConstraints $ Map.elems pairFacts]

    it "compile an imported graph to the same graph" $ do
        let graph = Document.compileGraph document
        Document.compileGraph <$> Document.fromGraph graph `shouldBe` Right graph
  where
    edited edits = either (error . Document.explainDocumentError) id $ Document.applyPatch (Document.patch document edits) document
    facts changed state =
        [ (FTA.transitionSymbol transition, Map.keys $ annotationFacts $ FTA.transitionConstraint transition)
        | transition <- rowOf state $ Document.sourceGraph changed
        ]
    annotations changed state = map FTA.transitionConstraint $ rowOf state $ Document.sourceGraph changed

-- | A pair of atoms whose production has three named facts.
document :: Document.Document State
document = either (error . Document.explainDocumentError) id $ Document.mkDocument Expr rows

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
