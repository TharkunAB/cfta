module Data.CFTA.Edit.BetweenSpec (spec) where

import Data.List (sort)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Edit
import Data.CFTA.Edit.Between
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (ChildIndex (..), Size (..), TransitionIndex (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Path (path)
import Data.CFTA.Sized (sized, termsOfSize)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Edit.Between" $ do
    it "finds every edit of the edit automaton, up to a size, and no other" $
        mapM_
            ( \(name, automaton, given) -> do
                let edits = concat [termsOfSize classes (Size size) | size <- [1 .. bound + 1]]
                    classes = either (error . show) id $ sized $ either (error . show) id $ editAutomaton automaton given
                    edited = [(edit, result) | edit <- edits, Just result <- [applyEdit given edit]]
                mapM_
                    ( \(edit, result) -> do
                        found <- either (fail . show) pure $ editsBetween automaton given result
                        (name, edit `elem` found) `shouldBe` (name, True)
                        -- The edits of the same size range that give the result are the ones the definition gives.
                        sort (filter ((<= fromInteger bound + 1) . length) found)
                            `shouldBe` sort [other | (other, otherResult) <- edited, otherResult == result]
                    )
                    edited
                (name, length edited > 10) `shouldBe` (name, True)
            )
            fixtures
    it "gives the replacements at the common ancestor and its ancestors for a change at two sites, and no wrap" $
        editsBetween expressions twoSites twoSitesNew
            `shouldBe` Right
                [ term (ReplaceAt (path [0])) [material "add" [lit' "two", lit' "two"]]
                , term (ReplaceAt (path [])) [material "add" [material "add" [lit' "two", lit' "two"], lit' "two"]]
                ]
    it "gives a replacement and a wrap for x to f(x)" $
        editsBetween expressions (lit "one") (Term.Node "neg" [lit "one"])
            `shouldBe` Right
                [ term (WrapAt (path []) "neg" (TransitionIndex 1) (ChildIndex 0)) []
                , term (ReplaceAt (path [])) [material "neg" [lit' "one"]]
                ]
    it "accepts the replacement and the wrap in the edit automaton" $ do
        let found = either (error . show) id $ editsBetween expressions (lit "one") (Term.Node "neg" [lit "one"])
            edits = either (error . show) id $ editAutomaton expressions (lit "one")
        map (FTA.accepts edits) found `shouldBe` [True, True]
    it "gives a replacement and a context wrap for x to f(g(x))" $
        editsBetween expressions (lit "one") (Term.Node "neg" [Term.Node "neg" [lit "one"]])
            `shouldBe` Right
                [ term (ContextAt (path []) "neg" (TransitionIndex 1) (ChildIndex 0)) [term (HoleParent "neg" (ChildIndex 0)) []]
                , term (ReplaceAt (path [])) [material "neg" [material "neg" [lit' "one"]]]
                ]
    it "gives an unwrap to delete a statement, and a context wrap to wrap a statement in an if" $ do
        let skip = Term.Node "skip" []
            nil = Term.Node "nil" []
            cons a b = Term.Node "cons" [a, b]
            unwrap = term (UnwrapAt (path [0]) (ChildIndex 1)) []
            wrapIf =
                term
                    (ContextAt (path [0, 0]) "if" (TransitionIndex 1) (ChildIndex 0))
                    [term (HoleParent "cons" (ChildIndex 0)) [material "nil" []]]
        take 1 (either (error . show) id $ editsBetween statements twoStatements (Term.Node "block" [cons skip nil]))
            `shouldBe` [unwrap]
        -- Two context wraps of size 3 give the term: the if around the statement, and the cons around an if over the old statement.
        let found =
                either (error . show) id $
                    editsBetween statements oneStatement (Term.Node "block" [cons (Term.Node "if" [cons skip nil]) nil])
        (wrapIf `elem` found, map length (take 2 found)) `shouldBe` (True, [3, 3])
    it "gives no unwrap to a child that the state does not accept" $
        -- A body is a non-empty list, so cons(skip, nil) is not replaced by nil there.
        editsBetween statements oneStatement (Term.Node "block" [Term.Node "nil" []]) `shouldBe` Right []
    it "gives the rank of each edit in the generator of the edit automaton, in rank order" $ do
        let edits = either (error . show) id $ editAutomaton expressions (lit "one")
            generator = Gen.fromAutomaton $ fromFTA edits
            ranked = either (error . show) id $ rankedEditsBetween expressions (lit "one") (Term.Node "neg" [lit "one"])
        map snd ranked `shouldBe` either (error . show) id (editsBetween expressions (lit "one") (Term.Node "neg" [lit "one"]))
        map fst ranked `shouldBe` sort (map fst ranked)
        map (\(rank, _) -> Gen.unrank generator rank) ranked `shouldBe` map (Right . snd) ranked
    describe "gives no edit for" $ do
        it "new material outside the vocabulary" $
            editsBetween expressions sum' (Term.Node "add" [lit "one", Term.Node "mul" [lit "two"]]) `shouldBe` Right []
        it "new material of the wrong category" $
            editsBetween pairs pairGiven (Term.Node "pair" [Term.Node "num" [Term.Node "one" []], Term.Node "one" []])
                `shouldBe` Right []
        it "two equal terms" $
            editsBetween expressions sum' sum' `shouldBe` Right []
    describe "rejects"
        $ it "an old term that the automaton does not accept"
        $ editsBetween expressions (Term.Node "one" []) sum' `shouldSatisfy` either (== BetweenEdit NotAccepted) (const False)

-- | The largest edit size, minus one, that the tests compare.
bound :: Integer
bound = 5

-- | The fixtures: an unambiguous automaton and a term that it accepts.
fixtures :: [(String, FTA.PlainFTA String String, Term String)]
fixtures =
    [ ("expressions", expressions, sum')
    , ("chains", fromRows "s" [("s", [leaf "a", node "f" ["s"]])], Term.Node "f" [Term.Node "f" [Term.Node "a" []]])
    , ("pairs", pairs, pairGiven)
    , ("statements", statements, twoStatements)
    ]

-- | Blocks of statements: a body is a non-empty list, and an if has a body.
statements :: FTA.PlainFTA String String
statements =
    fromRows
        "m"
        [ ("m", [node "block" ["b"]])
        , ("b", [node "cons" ["s", "l"]])
        , ("l", [leaf "nil", node "cons" ["s", "l"]])
        , ("s", [leaf "skip", node "if" ["b"]])
        ]

-- | A block of one statement, and a block of two.
oneStatement, twoStatements :: Term String
oneStatement = Term.Node "block" [Term.Node "cons" [Term.Node "skip" [], Term.Node "nil" []]]
twoStatements =
    Term.Node "block" [Term.Node "cons" [Term.Node "skip" [], Term.Node "cons" [Term.Node "skip" [], Term.Node "nil" []]]]

-- | Expressions: a literal of a number, a negation, or a sum.
expressions :: FTA.PlainFTA String String
expressions = fromRows "e" [("e", [node "lit" ["n"], node "neg" ["e"], node "add" ["e", "e"]]), ("n", [leaf "one", leaf "two"])]

-- | Pairs with a flag on either side.
pairs :: FTA.PlainFTA String String
pairs =
    fromRows
        "e"
        [ ("e", [node "num" ["n"], node "pair" ["e", "b"], node "pair" ["b", "e"]])
        , ("n", [leaf "one", leaf "two"])
        , ("b", [leaf "yes", leaf "no"])
        ]

pairGiven :: Term String
pairGiven = Term.Node "pair" [Term.Node "num" [Term.Node "one" []], Term.Node "yes" []]

-- | The sum add(lit(one), neg(lit(two))).
sum' :: Term String
sum' = Term.Node "add" [lit "one", Term.Node "neg" [lit "two"]]

-- | add(add(lit one, lit one), lit two), and the same with the inner sum changed at two sites.
twoSites, twoSitesNew :: Term String
twoSites = Term.Node "add" [Term.Node "add" [lit "one", lit "one"], lit "two"]
twoSitesNew = Term.Node "add" [Term.Node "add" [lit "two", lit "two"], lit "two"]

-- | A literal of a number.
lit :: String -> Term String
lit number = Term.Node "lit" [Term.Node number []]

-- | A literal of a number, as new material.
lit' :: String -> Term (EditSymbol String)
lit' number = material "lit" [material number []]

-- | An automaton from rows of named states.
fromRows :: String -> [(String, [FTA.Transition String String Constraint])] -> FTA.PlainFTA String String
fromRows initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A transition without children.
leaf :: String -> FTA.Transition String String Constraint
leaf symbol = FTA.Transition symbol [] noConstraint

-- | A transition without a constraint.
node :: String -> [String] -> FTA.Transition String String Constraint
node symbol children = FTA.Transition symbol children noConstraint

-- | An edit term from its symbol and children.
term :: EditSymbol String -> [Term (EditSymbol String)] -> Term (EditSymbol String)
term = Term.Node

-- | New material from its symbol and children.
material :: String -> [Term (EditSymbol String)] -> Term (EditSymbol String)
material = Term.Node . Material
