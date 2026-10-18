{-# LANGUAGE OverloadedStrings #-}

-- | The readable text format: exact round trips, stable printing, errors, and ranks.
module Main (main) where

import Control.Monad (forM_)
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
import Data.CFTA.Index (ClassRank (..))
import qualified Data.CFTA.Language as L
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Serialization.Text (StateCodec (..), TextError (..))
import qualified Data.CFTA.Serialization.Text as T
import qualified Data.CFTA.Sized as Sized
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
                roundTrip T.printLanguage T.parseLanguage $ withForms $ single name constraint

        it "keep structured states through Show and Read"
            $ roundTrip T.printLanguage T.parseLanguage
            $ withForms
            $ must
            $ D.mkDocument
                (Index (-3))
                [ (Index (-3), [production "f" [Group ["λ", "\"", "\n"]]])
                , (Group ["λ", "\"", "\n"], [production "leaf" []])
                ]

        it "keep states through an explicit codec" $
            forM_ graphs $ \(_, graph) ->
                roundTrip (T.printGraphWith strings) (T.parseGraphWith strings) graph

        it "ignore comments and whitespace" $ do
            let language = withForms $ document liquid
            T.parseLanguage ("// λ prefix\r\n\t" <> T.printLanguage language <> " // suffix") `shouldBe` Right language

        it "allow an edit after reopening" $ do
            let original = withForms $ single "leaf" $ Constraint (EqConstraints []) Bottom
                ref = L.at "leaf" "leaf"
                changes = L.define ref "replacement" [] <> L.relax ref "leaf" <> L.restore "0"
                reopened = must $ T.parseLanguage $ T.printLanguage original
            L.update reopened changes `shouldBe` L.update original changes

    describe "errors" $ do
        it "give the line and column of a syntax error" $
            case T.parseLanguageWith strings "// λ\nlanguage 1;\nstart S;\nstate S { a = a @{ nonsense }; }" of
                Left (SyntaxError line column _) -> (line, column) `shouldSatisfy` \(l, c) -> l == 4 && c > 20
                other -> expectationFailure $ show other

        it "report a duplicate state and a duplicate production" $ do
            T.parseLanguageWith strings "language 1; start S; state S {} state S {}"
                `shouldBe` Left (InvalidDefinition $ D.DuplicateState "S")
            T.parseLanguageWith strings "language 1; start S; state S { x = a; x = b; }"
                `shouldBe` Left (InvalidDefinition $ D.DuplicateTransition "S" "x")

        it "reject malformed input" $
            forM_ malformed $ \text ->
                T.parseLanguageWith strings text `shouldSatisfy` either (const True) (const False)

        it "explain a bad string escape" $
            forM_ escapes $ \(escape, expected) ->
                case T.parseLanguageWith strings $ "language 1; start \"" <> escape <> "\"; state S {}" of
                    Left failure -> Text.pack (T.explainTextError failure) `shouldSatisfy` Text.isInfixOf expected
                    Right _ -> expectationFailure $ "accepted " <> show escape

        it "keep the formats apart" $
            T.parseDocumentWith strings "language 1; start S; state S {}" `shouldSatisfy` either (const True) (const False)

    describe "graph quotes" $ do
        it "read like a graph without its first line" $
            forM_ graphs $ \(_, graph) -> do
                let printed = T.printGraphWith strings graph
                    body = Text.unlines $ drop 1 $ Text.lines printed
                T.parseGraphQuote Map.empty Map.empty body `shouldBe` T.parseGraphWith strings printed

        it "list their names once each" $
            T.graphQuoteNames "start S; state S { $a; $b(S) where $c; $a; }" `shouldBe` Right (["a", "b"], ["c"])

        it "put the values in place of the names" $
            T.parseGraphQuote
                (Map.fromList [("p", "pair")])
                (Map.fromList [("same", equal)])
                "start S; state S { $p(A, A) where $same; } state A { a; }"
                `shouldBe` Right (must $ FTA.mkFTA "S" [("S", [FTA.Transition "pair" ["A", "A"] equal]), ("A", [leaf "a"])])

        it "report an unknown name at its position" $
            case T.parseGraphQuote Map.empty Map.empty "start S;\nstate S { $a; }" of
                Left (SyntaxError line _ message) -> (line, message) `shouldSatisfy` \(l, m) -> l == 2 && "unknown symbol $a" `Text.isInfixOf` Text.pack m
                other -> expectationFailure $ show other

        it "check the state rows before the values are known" $ do
            T.graphQuoteNames "start T; state S {}"
                `shouldBe` Left (InvalidDefinition $ D.InvalidGraph $ FTA.MissingInitialState "T")
            T.graphQuoteNames "start S; state S { $a(T); }"
                `shouldBe` Left (InvalidDefinition $ D.InvalidGraph $ FTA.DanglingState "T")
            T.graphQuoteNames "start S; state S {} state S {}" `shouldBe` Left (InvalidDefinition $ D.DuplicateState "S")

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

    describe "ranks" $
        it "are the same after a round trip" $
            forM_ (filter ((/= "all-forms") . fst) graphs) $ \(_, graph) ->
                sameRanks graph $ must $ T.parseGraph $ T.printGraph graph

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

-- | State labels as plain text.
strings :: StateCodec String
strings = StateCodec Text.pack (Right . Text.unpack)

-- | Stop a test on an unexpected error.
must :: (Show failure) => Either failure value -> value
must = either (error . show) id

-- | A plain graph as a document.
document :: FTA.PlainFTA String Symbol -> D.Document String
document = must . D.fromGraph

-- | A production with no facts.
production :: Symbol -> [state] -> FTA.Transition state Symbol D.Annotation
production symbol children = FTA.Transition symbol children $ D.Annotation (symbolText symbol) Map.empty

-- | A one-state language whose name, symbol, and fact use the same text.
single :: Text -> Constraint -> D.Document String
single name constraint =
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
  where
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
