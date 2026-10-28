{-# LANGUAGE OverloadedStrings #-}

-- | The readable text format: exact round trips, stable printing, errors, and ranks.
module Main (main) where

import Control.Monad (forM_, void)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, hspec, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint (..),
    Guard (..),
    Substitution (..),
    conjoinConstraints,
    equalityConstraint,
    noConstraint,
    semanticConstraint,
 )
import qualified Data.CFTA.Document as D
import Data.CFTA.Equality.Constraint (
    EqConstraints (EqConstraints, EqContradiction),
    PathEClass (PathEClass),
    mkEqConstraints,
 )
import qualified Data.CFTA.Formula as F
import Data.CFTA.Index (ClassRank (..), Size, Weight)
import qualified Data.CFTA.Language as L
import qualified Data.CFTA.Merge as Merge
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Serialization.Text (StateCodec (..), TextError (..))
import qualified Data.CFTA.Serialization.Text as T
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Sized.Checkpoint (Checkpoint (..), CheckpointError (..), SamplingCheckpoint (..))
import qualified Data.CFTA.Sized.Checkpoint as Checkpoint
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol), symbolText, valueName)
import Data.CFTA.Template (Template (..))

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec spec

-- | A state with structure, printed and read through 'Show' and 'Read'.
data State = Index Int | Group [String]
    deriving (Eq, Ord, Show, Read)

spec :: Spec
spec = do
    describe "round trips" $ do
        it "keep every graph" $
            forM_ graphs $
                \(_, graph) -> roundTrip T.printGraph T.parseGraph graph

        it "keep every document" $
            forM_ graphs $
                \(_, graph) -> roundTrip T.printDocument T.parseDocument $ document graph

        it "keep every language with every template form" $
            forM_ graphs $
                \(_, graph) -> roundTrip T.printLanguage T.parseLanguage $ withForms $ document graph

        it "keep unusual names and stored constraints" $
            forM_ [(name, constraint) | name <- names, constraint <- storedConstraints] $ \(name, constraint) ->
                roundTrip T.printGraph T.parseGraph $ single name constraint

        it "keep unusual names and stored facts in a language" $
            forM_ [(name, constraint) | name <- names, constraint <- storedConstraints] $ \(name, constraint) ->
                roundTrip T.printLanguage T.parseLanguage $ withForms $ singleSource name constraint

        it "keep structured states through Show and Read"
            $ roundTrip T.printGraph T.parseGraph
            $ must
            $ FTA.mkFTA
                (Index (-3))
                [ (Index (-3), [FTA.Transition "f" [Group ["λ", "\"", "\n"]] noConstraint])
                , (Group ["λ", "\"", "\n"], [FTA.Transition "leaf" [] noConstraint])
                ]

        it "keep states through an explicit codec" $
            forM_ graphs $ \(_, graph) ->
                roundTrip (T.printGraphWith strings) (T.parseGraphWith strings) graph

        it "ignore comments and whitespace" $
            T.parseGraph ("// λ prefix\r\n\t" <> T.printGraph liquid <> " // suffix") `shouldBe` Right liquid

        it "allow an edit after reopening" $ do
            let original = withForms $ singleSource "leaf" $ Constraint (EqConstraints []) Bottom
                ref = L.at "leaf" "leaf"
                changes = L.define ref "replacement" [] <> L.relax ref "leaf" <> L.restore "0"
                reopened = must $ T.parseLanguage $ T.printLanguage original
            L.update reopened changes `shouldBe` L.update original changes

    describe "errors" $ do
        it "give the line and column of a syntax error" $
            case T.parseGraphWith strings "// λ\ngraph 1;\nstart S;\nstate S { a @{ nonsense }; }" of
                Left (SyntaxError line column _) -> (line, column) `shouldSatisfy` \(l, c) -> l == 4 && c > 15
                other -> expectationFailure $ show other

        it "report a duplicate state" $
            T.parseGraphWith strings "graph 1; start S; state S {} state S {}" `shouldBe` Left (DuplicateState "S")

        it "report a duplicate state and a duplicate production in a language" $ do
            T.parseLanguageWith strings "language 1; start S; state S {} state S {}"
                `shouldBe` Left (InvalidDefinition $ D.DuplicateState "S")
            T.parseLanguageWith strings "language 1; start S; state S { x = a; x = b; }"
                `shouldBe` Left (InvalidDefinition $ D.DuplicateTransition "S" "x")

        it "reject malformed input" $
            forM_ malformed $ \text ->
                T.parseGraphWith strings text `shouldSatisfy` either (const True) (const False)

        it "reject malformed languages" $
            forM_ malformedLanguages $ \text ->
                T.parseLanguageWith strings text `shouldSatisfy` either (const True) (const False)

        it "explain a bad string escape" $
            forM_ escapes $ \(escape, expected) ->
                case T.parseGraphWith strings $ "graph 1; start \"" <> escape <> "\"; state S {}" of
                    Left failure -> Text.pack (T.explainTextError failure) `shouldSatisfy` Text.isInfixOf expected
                    Right _ -> expectationFailure $ "accepted " <> show escape

        it "keep the formats apart" $
            T.parseDocumentWith strings "language 1; start S; state S {}" `shouldSatisfy` either (const True) (const False)

    describe "updates" $ do
        it "keep every operation" $
            roundTrip (T.printUpdateWith strings) (T.parseUpdateWith strings) everyOperation

        it "give the same language when they are applied after reopening" $ do
            let language = withForms $ document liquid
                reopened = must $ T.parseUpdateWith strings $ T.printUpdateWith strings everyOperation
            L.update language reopened `shouldBe` L.update language everyOperation
            L.update language everyOperation `shouldSatisfy` either (const False) (const True)

        it "give the position of an error" $
            case T.parseUpdateWith strings "update 1;\ndefine pair t0 = pair(atom, atom);\nrequire pair t0;" of
                Left (SyntaxError line _ _) -> line `shouldBe` 3
                other -> expectationFailure $ show other

    describe "merges" $ do
        it "keep a merged language" $ do
            roundTrip T.printLanguage T.parseLanguage merged
            roundTrip (T.printLanguageWith strings) (T.parseLanguageWith strings) merged

        it "give the same merge after the three versions are printed and read" $ do
            let reopen = must . T.parseLanguageWith strings . T.printLanguageWith strings
            Merge.merge3 (reopen mergeBase) (reopen mergeLeft) (reopen mergeRight) `shouldBe` Right merged
            merged `shouldBe` must (L.update mergeBase $ leftChanges <> rightChanges)

        it "give each version from the base with a difference that is printed and read" $
            forM_ [mergeLeft, mergeRight, merged, must $ L.update mergeBase $ L.start "atom"] $ \other -> do
                let printed = T.printUpdateWith strings $ Merge.diff mergeBase other
                L.update mergeBase (must $ T.parseUpdateWith strings printed) `shouldBe` Right other

    describe "ranks" $
        it "are the same after a round trip" $
            forM_ (filter ((/= "all-forms") . fst) graphs) $ \(_, graph) ->
                sameRanks graph $ must $ T.parseGraph $ T.printGraph graph

    describe "checkpoints" $ do
        it "resume at every cut as the listing without a cut, after the checkpoint and the graph are printed and read" $
            forM_ listed $ \graph -> do
                let entries = must $ Checkpoint.resume (Checkpoint.start 7 graph) graph
                    listing = map fst entries
                    reopened = must $ T.parseGraphWith strings $ T.printGraphWith strings graph
                forM_ (zip [0 ..] $ Checkpoint.start 7 graph : map snd entries) $ \(cut, checkpoint) -> do
                    let saved = must $ T.parseCheckpointWith strings $ T.printCheckpointWith strings checkpoint
                    (take cut listing <>) . map fst <$> Checkpoint.resume saved reopened `shouldBe` Right listing

        it "reject a checkpoint for an edited graph as stale" $ do
            let edited = must $ FTA.replaceRows (Map.singleton "q" $ Just [FTA.Transition "n" ["leaf"] noConstraint]) ordinary
                saved = must $ T.parseCheckpoint $ T.printCheckpoint $ Checkpoint.start 7 ordinary
            void (Checkpoint.resume saved edited) `shouldBe` Left (StaleRow "q")
            void (Checkpoint.resume saved ordinary) `shouldBe` Right ()

        it "reject a guard beyond equality constraints, which needs a solver" $
            void (Checkpoint.resume (Checkpoint.start 7 liquid) liquid) `shouldBe` Left (QueryFailed Sized.ResidualGuard)

        it "keep every checkpoint" $
            forM_ checkpoints $ \checkpoint -> do
                roundTrip T.printCheckpoint T.parseCheckpoint checkpoint
                roundTrip (T.printCheckpointWith strings) (T.parseCheckpointWith strings) checkpoint

        it "print the query and the next sized rank, then the printed graph" $ do
            let printed = T.printCheckpointWith strings (Checkpoint.start 7 trees){checkpointNext = (5, 1)}
            printed
                `shouldBe` Text.unlines
                    [ "checkpoint 1;"
                    , "query sized 1;"
                    , "bound 7;"
                    , "next 5 1;"
                    , ""
                    , "graph 1;"
                    , "start tree;"
                    , ""
                    , "state tree {"
                    , "  leaf;"
                    , "  node(tree, tree);"
                    , "}"
                    , ""
                    ]
            printed `shouldSatisfy` Text.isSuffixOf (T.printGraphWith strings trees)

        it "give the line of a syntax error" $ do
            case T.parseCheckpointWith strings "checkpoint 1;\nquery sized 1;\nbound 7;\nnext 5;\n\ngraph 1;\nstart s;\nstate s {}" of
                Left (SyntaxError line _ _) -> line `shouldBe` 4
                other -> expectationFailure $ show other
            T.parseCheckpointWith strings "checkpoint 2;\nquery sized 1;\nbound 7;\nnext 1 0;\ngraph 1;\nstart s;\nstate s {}"
                `shouldSatisfy` either (const True) (const False)

    describe "sampling checkpoints" $ do
        it "resume at every cut as the run without a cut, after the checkpoint and the graph are printed and read" $
            forM_ [(graph, weights) | graph <- listed, FTA.initialState graph /= "empty", weights <- [Nothing, Just drawWeights]] $
                \(graph, weights) -> do
                    let start = Checkpoint.startSampling 7 weights 11 graph
                        entries = take 30 $ must $ Checkpoint.resumeSampling start graph weights
                        run = map fst entries
                        reopened = must $ T.parseGraphWith strings $ T.printGraphWith strings graph
                    forM_ (zip [0 ..] $ start : map snd entries) $ \(cut, checkpoint) -> do
                        let saved = must $ T.parseSamplingCheckpointWith strings $ T.printSamplingCheckpointWith strings checkpoint
                        (take cut run <>) . take (30 - cut) . map fst <$> Checkpoint.resumeSampling saved reopened weights
                            `shouldBe` Right run

        it "reject a sampling checkpoint for an edited graph or other weights" $ do
            let edited = must $ FTA.replaceRows (Map.singleton "q" $ Just [FTA.Transition "n" ["leaf"] noConstraint]) ordinary
                saved = must $ T.parseSamplingCheckpoint $ T.printSamplingCheckpoint $ Checkpoint.startSampling 7 Nothing 11 ordinary
            void (Checkpoint.resumeSampling saved edited Nothing) `shouldBe` Left (StaleRow "q")
            void (Checkpoint.resumeSampling saved ordinary $ Just drawWeights) `shouldBe` Left StaleWeights
            void (Checkpoint.resumeSampling saved ordinary Nothing) `shouldBe` Right ()

        it "keep every sampling checkpoint" $
            forM_ samplingCheckpoints $ \checkpoint -> do
                roundTrip T.printSamplingCheckpoint T.parseSamplingCheckpoint checkpoint
                roundTrip (T.printSamplingCheckpointWith strings) (T.parseSamplingCheckpointWith strings) checkpoint

        it "print the query, the weights, and the position of the run, then the printed graph" $ do
            let weighted = Checkpoint.startSampling 7 (Just $ Map.fromList [(1, 1), (5, 3)]) 11 trees
                printed = T.printSamplingCheckpointWith strings weighted{samplingDraws = 12}
            printed
                `shouldBe` Text.unlines
                    [ "sampling 1;"
                    , "query sized-sample 1;"
                    , "bound 7;"
                    , "weights [1: 1, 5: 3];"
                    , "prng splitmix64 1;"
                    , "seed 11;"
                    , "draws 12;"
                    , ""
                    , "graph 1;"
                    , "start tree;"
                    , ""
                    , "state tree {"
                    , "  leaf;"
                    , "  node(tree, tree);"
                    , "}"
                    , ""
                    ]
            T.printSamplingCheckpointWith strings (Checkpoint.startSampling 7 Nothing 11 trees)
                `shouldSatisfy` Text.isInfixOf "\nweights uniform;\n"

        it "give the line of a syntax error" $ do
            let header seed weights =
                    "sampling 1;\nquery sized-sample 1;\nbound 7;\nweights "
                        <> weights
                        <> ";\nprng splitmix64 1;\nseed "
                        <> seed
                        <> ";\ndraws 0;\n\ngraph 1;\nstart s;\nstate s {}"
                lineOf text = case T.parseSamplingCheckpointWith strings text of
                    Left (SyntaxError line _ _) -> Just line
                    _ -> Nothing
            lineOf (header "18446744073709551615" "uniform") `shouldBe` Nothing
            lineOf (header "18446744073709551616" "uniform") `shouldBe` Just 6
            lineOf (header "-1" "uniform") `shouldBe` Just 6
            lineOf (header "0" "[1: 1, 1: 2]") `shouldBe` Just 4
            lineOf ("sampling 2;" <> Text.drop (Text.length "sampling 1;") (header "0" "uniform")) `shouldBe` Just 1

-- | The graphs whose listing needs no solver, and a recursive graph with equal children.
listed :: [FTA.PlainFTA String Symbol]
listed =
    [graph | (name, graph) <- graphs, name `elem` ["ordinary", "recursive", "equality", "empty"]]
        <> [ must $
                FTA.mkFTA "s" [("s", [leaf "a", leaf "b", FTA.Transition "f" ["s"] noConstraint, FTA.Transition "g" ["s", "s"] equal])]
           ]

-- | A checkpoint for each graph, and checkpoints with unusual route names and large or negative numbers.
checkpoints :: [Checkpoint String]
checkpoints =
    [Checkpoint.start 7 graph | (_, graph) <- graphs]
        <> [ (Checkpoint.start 7 ordinary)
                { checkpointRoute = name
                , checkpointVersion = -1
                , checkpointBound = 10 ^ (30 :: Int)
                , checkpointNext = (10 ^ (40 :: Int), 2 ^ (100 :: Int))
                }
           | name <- names
           ]

-- | Weights of sizes up to seven, with a size of no terms in some graphs.
drawWeights :: Map.Map Size Weight
drawWeights = Map.fromList [(1, 1), (3, 2), (6, 1), (7, 5)]

{- | A sampling checkpoint for each graph and each form of weights, and
sampling checkpoints with unusual names and large or negative numbers.
-}
samplingCheckpoints :: [SamplingCheckpoint String]
samplingCheckpoints =
    [ Checkpoint.startSampling 7 weights seed graph
    | (_, graph) <- graphs
    , (weights, seed) <- [(Nothing, 0), (Just drawWeights, maxBound), (Just Map.empty, 11)]
    ]
        <> [ (Checkpoint.startSampling (10 ^ (30 :: Int)) (Just unusual) 11 ordinary)
                { samplingRoute = name
                , samplingVersion = -1
                , samplingPrng = name
                , samplingPrngVersion = 2 ^ (100 :: Int)
                , samplingDraws = 2 ^ (100 :: Int)
                }
           | name <- names
           ]
  where
    unusual = Map.fromList [(-2, -5), (0, 0), (10 ^ (30 :: Int), 2 ^ (100 :: Int))]

-- | Binary trees: a leaf, or a node with two trees.
trees :: FTA.PlainFTA String Symbol
trees = must $ FTA.mkFTA "tree" [("tree", [leaf "leaf", FTA.Transition "node" ["tree", "tree"] noConstraint])]

-- | Print and parse again: the value is the same, and so is the text.
roundTrip ::
    (Eq value, Show value, Show failure, Eq failure) =>
    (value -> Text) -> (Text -> Either failure value) -> value -> Expectation
roundTrip printer parser value = do
    let printed = printer value
    parser printed `shouldBe` Right value
    fmap printer (parser printed) `shouldBe` Right printed

-- | Compare the counts, the terms in order, and the rank maps up to size seven.
sameRanks :: FTA.PlainFTA String Symbol -> FTA.PlainFTA String Symbol -> Expectation
sameRanks before after = withZ3 [] $ \solver -> do
    old <- Sized.sizedUpTo solver 7 before >>= either (fail . show) pure
    new <- Sized.sizedUpTo solver 7 after >>= either (fail . show) pure
    forM_ [1 .. 7] $ \size -> do
        Sized.countOfSize new size `shouldBe` Sized.countOfSize old size
        Sized.termsOfSize new size `shouldBe` Sized.termsOfSize old size
        forM_ (zip [0 ..] $ Sized.termsOfSize old size) $ \(rank, term) -> do
            Sized.unrankOfSize new size (ClassRank rank) `shouldBe` Just term
            Sized.rankOfSize new term `shouldBe` Just (size, ClassRank rank)

-- | The base of the merge tests: the language of 'liquid' with every template form.
mergeBase :: L.Language String
mergeBase = withForms $ document liquid

-- | A new fact and a new exclusion.
leftChanges :: L.Update String
leftChanges = L.require (L.at "pair" "t0") "same" equal <> L.without "extra" (L.AtRoot Hole)

-- | A new production, a removed fact, and a restored exclusion.
rightChanges :: L.Update String
rightChanges =
    L.define (L.at "atom" "two") (RefinedSymbol "two" $ refinementFormula (.== 2)) []
        <> L.relax (L.at "atom" "t1") "imported"
        <> L.restore "0"

-- | The two sides of the merge tests, and their merge.
mergeLeft, mergeRight, merged :: L.Language String
mergeLeft = must $ L.update mergeBase leftChanges
mergeRight = must $ L.update mergeBase rightChanges
merged = must $ Merge.merge3 mergeBase mergeLeft mergeRight

-- | An update with every operation, valid on the language of 'liquid' with every template form.
everyOperation :: L.Update String
everyOperation =
    L.define (L.at "atom" "two") (RefinedSymbol "two" $ refinementFormula (.== 2)) []
        <> L.require (L.at "pair" "t0") "same" equal
        <> L.relax (L.at "pair" "t0") "imported"
        <> L.remove (L.at "atom" "t1")
        <> L.editSource
            ( D.PutTransition "atom"
                $ FTA.Transition "three" []
                $ D.Annotation "three"
                $ Map.singleton "never"
                $ Constraint (EqConstraints []) Bottom
            )
        <> L.editSource (D.PutRow "extra" [production "leaf" []])
        <> L.editSource (D.DeleteRow "extra")
        <> L.without "pairs" (L.AtRoot $ TemplateNode "pair" [Hole, Hole])
        <> L.restore "0"
        <> L.start "atom"

-- | State labels as plain text.
strings :: StateCodec String
strings = StateCodec Text.pack (Right . Text.unpack)

-- | Stop a test on an unexpected error.
must :: (Show failure) => Either failure value -> value
must = either (error . show) id

-- | A one-state graph whose state, symbol, and refinement bound use the same name, and a dead state.
single :: Text -> Constraint -> FTA.PlainFTA String Symbol
single name constraint =
    must $
        FTA.mkFTA
            (Text.unpack name)
            [
                ( Text.unpack name
                , [FTA.Transition (RefinedSymbol (Symbol name) $ F.Atom F.Eq value (F.Lit $ 2 ^ (100 :: Int))) [] constraint]
                )
            , ("dead", [])
            ]
  where
    value = F.Var $ F.Name $ Text.pack valueName

-- | A plain graph as a document.
document :: FTA.PlainFTA String Symbol -> D.Document String
document = must . D.fromGraph

-- | A production with no facts.
production :: Symbol -> [state] -> FTA.Transition state Symbol D.Annotation
production symbol children = FTA.Transition symbol children $ D.Annotation (symbolText symbol) Map.empty

-- | A one-state language whose name, symbol, and fact use the same text.
singleSource :: Text -> Constraint -> D.Document String
singleSource name constraint =
    must $
        D.mkDocument
            (Text.unpack name)
            [
                ( Text.unpack name
                ,
                    [ FTA.Transition (RefinedSymbol (Symbol name) $ F.Atom F.Eq value (F.Lit $ 2 ^ (100 :: Int))) []
                        $ D.Annotation name
                        $ Map.singleton name constraint
                    ]
                )
            , ("dead", [])
            ]
  where
    value = F.Var $ F.Name $ Text.pack valueName

-- | The language with one named exclusion for each template form, at the root and anywhere.
withForms :: D.Document state -> L.Language state
withForms source =
    L.Language source $
        Map.fromList
            [ (L.ExclusionName $ Text.pack $ show index, scope form)
            | (index, (scope, form)) <- zip [0 :: Int ..] [(scope, form) | scope <- [L.AtRoot, L.Anywhere], form <- forms]
            ]
  where
    forms =
        [ Hole
        , AnyNode []
        , AnyNode [Hole]
        , AnyPrefix []
        , AnyPrefix [Hole]
        , TemplateNode "_" []
        , TemplateNode "json" [Hole]
        , TemplatePrefix "_" []
        , TemplatePrefix "f" [Hole]
        , TemplateNode (RefinedSymbol "x" $ F.And []) [AnyPrefix [], TemplatePrefix "a b" [Hole]]
        ]

-- | Names that need quotes or escapes, or that look like keywords.
names :: [Text]
names =
    [ ""
    , "_"
    , "_foo"
    , "json"
    , "language"
    , "a-b"
    , "+"
    , "123"
    , "a b"
    , "λ"
    , "😀"
    , "line\nquote\"\\\0\b\f"
    , "v"
    , "true"
    , "raw"
    , "//keep"
    ]

-- | Constraints whose stored form differs from their meaning.
storedConstraints :: [Constraint]
storedConstraints =
    [ noConstraint
    , Constraint (EqConstraints []) Bottom
    , Constraint EqContradiction Top
    , Constraint EqContradiction Bottom
    , Constraint (EqConstraints [PathEClass Set.empty]) Top
    , Constraint (EqConstraints [PathEClass $ Set.singleton $ path []]) Top
    , Constraint
        (EqConstraints [PathEClass $ Set.fromList [path [0], path [1]], PathEClass $ Set.fromList [path [1], path [2]]])
        Top
    , Constraint (EqConstraints []) (Satisfies (path [-1, 2]) $ F.And [])
    ]

-- | The test graphs: dead and unreachable rows, repeated alternatives, recursion, constraints, and every logical form.
graphs :: [(String, FTA.PlainFTA String Symbol)]
graphs =
    [ ("ordinary", ordinary)
    , ("recursive", must $ FTA.mkFTA "s" [("s", [leaf "a", leaf "b", FTA.Transition "f" ["s", "s"] noConstraint])])
    , ("equality", pairs equal)
    , ("liquid", liquid)
    , ("empty", must $ FTA.mkFTA "empty" [("empty", [])])
    , ("all-forms", allForms)
    ]

-- | A graph with a dead row, an unreachable row, and a repeated alternative.
ordinary :: FTA.PlainFTA String Symbol
ordinary =
    must $
        FTA.mkFTA
            "s"
            [ ("s", [FTA.Transition "f" ["p"] noConstraint, FTA.Transition "f" ["q"] noConstraint])
            , ("p", [FTA.Transition "a" ["dead"] noConstraint, FTA.Transition "z" ["leaf"] noConstraint])
            , ("q", [FTA.Transition "m" ["leaf"] noConstraint])
            , ("leaf", [leaf "k", leaf "k"])
            , ("dead", [])
            , ("unreachable", [leaf "unused"])
            ]

-- | Pairs of atoms with a refinement each, under a constraint.
liquid :: FTA.PlainFTA String Symbol
liquid = pairs $ conjoinConstraints equal $ semanticConstraint $ Satisfies (path [0]) $ refinementFormula (.> 0)

-- | Two atoms in a pair, under the given constraint.
pairs :: Constraint -> FTA.PlainFTA String Symbol
pairs constraint =
    must $
        FTA.mkFTA
            "pair"
            [ ("pair", [FTA.Transition "pair" ["atom", "atom"] constraint])
            ,
                ( "atom"
                , [leaf $ RefinedSymbol "zero" $ refinementFormula (.== 0), leaf $ RefinedSymbol "one" $ refinementFormula (.== 1)]
                )
            ]

-- | The two children are equal.
equal :: Constraint
equal = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]

-- | A leaf with no constraint.
leaf :: Symbol -> FTA.Transition String Symbol Constraint
leaf symbol = FTA.Transition symbol [] noConstraint

-- | One state with a leaf for each combination of formula, guard, and equality classes.
allForms :: FTA.PlainFTA String Symbol
allForms =
    must $
        FTA.mkFTA
            "schema"
            [
                ( "schema"
                , [ FTA.Transition (RefinedSymbol (Symbol $ Text.pack $ "σ\n\"\\" <> show index) formula) [] (Constraint classes guard)
                  | (index, (formula, guard, classes)) <-
                        zip [0 :: Int ..] [(f, g, c) | (f, g) <- zip (cycle formulas) guards, c <- classCases]
                  ]
                )
            ]
  where
    classCases =
        [ EqContradiction
        , EqConstraints []
        , EqConstraints [PathEClass $ Set.fromList [path [0], path [1]], PathEClass Set.empty]
        , EqConstraints [PathEClass $ Set.singleton $ path [-1, 2]]
        ]

-- | Every formula constructor, every relation, and every term constructor.
formulas :: [F.Formula]
formulas =
    [F.Top, F.Bottom, F.And [], F.Or [], F.And [F.Top, F.Bottom], F.Or [F.Bottom, F.Top], F.Not F.Bottom]
        <> [F.Atom relation term (F.Var "v") | relation <- [F.Eq, F.Ne, F.Gt, F.Ge, F.Lt, F.Le], term <- terms]
        <> [F.Forall bindings F.Top, F.Exists bindings F.Bottom]
  where
    bindings = [("x", F.IntSort), ("x", F.BoolSort), ("fn", F.FunctionSort [F.IntSort, F.RealSort] F.BoolSort)]
    terms =
        [ F.Lit (10 ^ (100 :: Int))
        , F.Lit (-(10 ^ (100 :: Int)))
        , F.Lit 0
        , F.Var "v\n\"\\"
        , F.App "fun" [F.Lit 1]
        , F.Neg x
        , F.Add x x
        , F.Sub x x
        , F.Mul x x
        , F.Div x x
        , F.Mod x x
        , F.Ite F.Top x x
        , F.Cast x F.RealSort
        ]
    x = F.Var "v"

-- | Every guard constructor, with each formula under 'Satisfies' and 'Holds'.
guards :: [Guard]
guards =
    [ Top
    , Bottom
    , Same (path []) (path [0])
    , Entails (path [0]) (path [1])
    , Not (Same (path [0]) (path [1]))
    , And []
    , Or []
    , And [Top, Bottom]
    , Or [Top, Bottom]
    , Substitute [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])] Top
    ]
        <> [Satisfies (path [-1, 0]) formula | formula <- formulas]
        <> [Holds [path [], path [2]] formula | formula <- formulas]

-- | Input that the parser must reject.
malformed :: [Text]
malformed =
    [ "graph 2; start S; state S {}"
    , "graph1; start S; state S {}"
    , "graph 1; start S; state S { f(Missing); }"
    , "graph 1; start S; state S { a; a(S); }"
    , "graph 1; start S; state S { a @{ v == 1.5 }; }"
    , "graph 1; start S; state S { a where raw {}; }"
    , "graph 1; start S; state S { a"
    , "graph 1; start S; state S {} garbage"
    , "graph 1; start S; state S { a where equal([9223372036854775808]); }"
    , "graph 1; start S; state S { a where satisfies([], forall([x: unknown], true)); }"
    , "graph 1; start S; state S { a where same([], [], []); }"
    ]

-- | Language input that the parser must reject.
malformedLanguages :: [Text]
malformedLanguages =
    [ "language 2; start S; state S {}"
    , "language1; start S; state S {}"
    , "language 1; start S; state S { a = a { x = true; x = false; }; }"
    , blank <> " exclude x = root _; exclude x = root _;"
    , "language 1; start S; state S { x = f(Missing); }"
    , "language 1; start S; state S { x = a; y = a(S); }"
    , blank <> " exclude x = elsewhere _;"
    , blank <> " exclude x = root f(...,a);"
    , blank <> " exclude x = root f(a,);"
    , "language 1; start S; state S { a = a @{ v == 1.5 }; }"
    , "language 1; start S; state S { a = a { x = raw {}; }; }"
    , "language 1; start S; state S { a = a"
    , blank <> " garbage"
    , "language 1; start S; state S { a = a { x = equal([9223372036854775808]); }; }"
    , "language 1; start S; state S { a = a { x = satisfies([], forall([x: unknown], true)); }; }"
    , "language 1; start S; state S { a = a { x = same([], [], []); }; }"
    ]
  where
    blank = "language 1; start S; state S {}"

-- | Bad string escapes and a part of the message that explains each one.
escapes :: [(Text, Text)]
escapes =
    [ ("\\q", "unknown string escape")
    , ("\\uDC00", "unexpected low surrogate")
    , ("\\uD800\\u0000", "expected a low surrogate")
    , ("\\uGGGG", "four hexadecimal digits")
    ]
