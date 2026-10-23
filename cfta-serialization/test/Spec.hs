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
import Data.CFTA.Equality.Constraint (
    EqConstraints (EqConstraints, EqContradiction),
    PathEClass (PathEClass),
    mkEqConstraints,
 )
import qualified Data.CFTA.Formula as F
import Data.CFTA.Index (ClassRank (..))
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Serialization.Text (StateCodec (..), TextError (..))
import qualified Data.CFTA.Serialization.Text as T
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Sized.Checkpoint (Checkpoint (..), CheckpointError (..))
import qualified Data.CFTA.Sized.Checkpoint as Checkpoint
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol), valueName)

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

        it "keep unusual names and stored constraints" $
            forM_ [(name, constraint) | name <- names, constraint <- storedConstraints] $ \(name, constraint) ->
                roundTrip T.printGraph T.parseGraph $ single name constraint

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

    describe "errors" $ do
        it "give the line and column of a syntax error" $
            case T.parseGraphWith strings "// λ\ngraph 1;\nstart S;\nstate S { a @{ nonsense }; }" of
                Left (SyntaxError line column _) -> (line, column) `shouldSatisfy` \(l, c) -> l == 4 && c > 15
                other -> expectationFailure $ show other

        it "report a duplicate state" $
            T.parseGraphWith strings "graph 1; start S; state S {} state S {}" `shouldBe` Left (DuplicateState "S")

        it "reject malformed input" $
            forM_ malformed $ \text ->
                T.parseGraphWith strings text `shouldSatisfy` either (const True) (const False)

        it "explain a bad string escape" $
            forM_ escapes $ \(escape, expected) ->
                case T.parseGraphWith strings $ "graph 1; start \"" <> escape <> "\"; state S {}" of
                    Left failure -> Text.pack (T.explainTextError failure) `shouldSatisfy` Text.isInfixOf expected
                    Right _ -> expectationFailure $ "accepted " <> show escape

    describe "doc comments" $ do
        it "keep the comments of a graph and of its states" $
            forM_ graphs $ \(_, graph) ->
                roundTrip
                    (uncurry $ T.printGraphNotesWith strings)
                    (T.parseGraphNotesWith strings)
                    (noted $ graphComments graph, graph)

        it "print no comment of an item that the value does not have" $
            T.parseGraphNotesWith
                strings
                (T.printGraphNotesWith strings (noted $ graphComments liquid <> Map.singleton (T.OnState "missing") "x") liquid)
                `shouldBe` Right (noted $ graphComments liquid, liquid)

        it "leave the text of the printers without comments unchanged" $
            forM_ graphs $ \(_, graph) ->
                T.printGraphNotesWith strings mempty graph `shouldBe` T.printGraphWith strings graph

        it "are dropped by the readers without comments" $
            T.parseGraphWith strings (T.printGraphNotesWith strings (noted $ graphComments liquid) liquid) `shouldBe` Right liquid

        it "need exactly three slashes" $
            T.parseGraphNotesWith strings "//// not a doc comment\n// nor this\ngraph 1; start S; state S {}"
                `shouldBe` Right (mempty, must $ FTA.mkFTA "S" [("S", [])])

        it "must come before the header or a state" $
            forM_ misplacedGraphComments $ \text ->
                case T.parseGraphWith strings text of
                    Left failure -> Text.pack (T.explainTextError failure) `shouldSatisfy` Text.isInfixOf "doc comment"
                    Right _ -> expectationFailure $ "accepted " <> show text

    describe "sorts" $ do
        it "keep the sorts of the states of a graph, with its doc comments" $
            forM_ graphs $ \(_, graph) ->
                roundTrip
                    (uncurry $ T.printGraphNotesWith strings)
                    (T.parseGraphNotesWith strings)
                    (noted (graphComments graph) <> sorted graph, graph)

        it "print no sort of a state that the graph does not have" $
            T.parseGraphNotesWith
                strings
                (T.printGraphNotesWith strings (sorted liquid <> mempty{T.noteSorts = Map.singleton "missing" "Int"}) liquid)
                `shouldBe` Right (sorted liquid, liquid)

        it "are dropped by the readers without notes" $
            T.parseGraphWith strings (T.printGraphNotesWith strings (sorted liquid) liquid) `shouldBe` Right liquid

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
            let graph = must $ FTA.mkFTA "tree" [("tree", [leaf "leaf", FTA.Transition "node" ["tree", "tree"] noConstraint])]
                printed = T.printCheckpointWith strings (Checkpoint.start 7 graph){checkpointNext = (5, 1)}
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
            printed `shouldSatisfy` Text.isSuffixOf (T.printGraphWith strings graph)

        it "give the line of a syntax error" $ do
            case T.parseCheckpointWith strings "checkpoint 1;\nquery sized 1;\nbound 7;\nnext 5;\n\ngraph 1;\nstart s;\nstate s {}" of
                Left (SyntaxError line _ _) -> line `shouldBe` 4
                other -> expectationFailure $ show other
            T.parseCheckpointWith strings "checkpoint 2;\nquery sized 1;\nbound 7;\nnext 1 0;\ngraph 1;\nstart s;\nstate s {}"
                `shouldSatisfy` either (const True) (const False)

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

-- | A comment on the file and on each state of a graph, from 'commentTexts' in turn.
graphComments :: FTA.PlainFTA String Symbol -> Map.Map (T.CommentTarget String) Text
graphComments graph =
    Map.fromList $ zip (T.OnFile : map T.OnState (Map.keys $ FTA.transitionTable graph)) (cycle commentTexts)

-- | Notes with only these doc comments.
noted :: Map.Map (T.CommentTarget String) Text -> T.Notes String
noted comments = mempty{T.noteComments = comments}

-- | Notes with a sort for each state of a graph, from 'names' in turn.
sorted :: FTA.FTA String Symbol annotation -> T.Notes String
sorted graph = mempty{T.noteSorts = Map.fromList $ zip (Map.keys $ FTA.transitionTable graph) (cycle names)}

-- | Comment texts with empty lines, spaces at either end, slashes, carriage returns, and Unicode.
commentTexts :: [Text]
commentTexts = ["plain", "", " leading space", "/ slash", "two\nlines", "\n", "λ 😀 \"quoted\"", "trailing space ", "a\r\nb"]

-- | Doc comments with no item after them, in a graph.
misplacedGraphComments :: [Text]
misplacedGraphComments =
    [ "graph 1;\n/// x\nstart S; state S {}"
    , "graph 1; start S; state S {}\n/// x\n"
    , "graph 1; start S; state S { a; /// x\n}"
    , "graph 1; start S; state S { /// x\na; }"
    , "graph 1; start S; state /// x\nS {}"
    , "graph 1; start S; state S : /// x\nInt {}"
    , "graph 1 /// x\n; start S; state S {}"
    ]

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

-- | Bad string escapes and a part of the message that explains each one.
escapes :: [(Text, Text)]
escapes =
    [ ("\\q", "unknown string escape")
    , ("\\uDC00", "unexpected low surrogate")
    , ("\\uD800\\u0000", "expected a low surrogate")
    , ("\\uGGGG", "four hexadecimal digits")
    ]
