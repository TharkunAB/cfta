module Data.CFTA.Edit.BetweenSpec (spec) where

import Control.Monad (forM_)
import Data.List (sort)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Edit
import Data.CFTA.Edit.Between
import Data.CFTA.Edit.Internal (sitePath)
import Data.CFTA.Edit.Sets (SetSymbol (..), applyEditSet, editSetAutomaton, editsOfSet)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (ChildIndex (..), Size (..), TransitionIndex (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Path (Path, path)
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
    describe "edit sets" $ do
        it "finds every edit set of one or two edits, up to a size, and no other" $
            forM_ fixtures $ \(name, automaton, given) -> forM_ [1, 2] $ \k -> do
                let sets = either (error . show) id $ editSetAutomaton k automaton given
                    classes = either (error . show) id $ sized sets
                    found = concat [termsOfSize classes (Size size) | size <- [1 .. setLimit k]]
                    edited = [(set, result) | set <- found, Just result <- [applyEditSet given set]]
                forM_ edited $ \(set, result) -> do
                    between <- either (fail . show) pure $ editSetsBetween k automaton given result
                    ((name, k), set `elem` between) `shouldBe` ((name, k), True)
                    -- The edit sets of the same size range that give the result are the ones of the automaton.
                    sort (filter ((<= fromInteger (setLimit k)) . length) between)
                        `shouldBe` sort [other | (other, otherResult) <- edited, otherResult == result]
                ((name, k), length edited > 10) `shouldBe` ((name, k), True)
        it "gives the edits of editsBetween as its sets of one edit" $
            forM_ [1, 2, 3] $ \k ->
                [ edits | Just edits@[_] <- map editsOfSet $ either (error . show) id $ editSetsBetween k expressions twoSites twoSitesNew
                ]
                    `shouldBe` map pure (either (error . show) id $ editsBetween expressions twoSites twoSitesNew)
        it "gives the two replacements of a change at two sites, and the replacements at the common ancestor and above" $ do
            -- The smallest first: the two leaves (4 nodes), a leaf and a literal (5), two literals and the inner sum (6), the whole term (8).
            let found = either (error . show) id $ editSetsBetween 2 expressions twoSites twoSitesNew
                atLeaves =
                    Term.Node
                        (Link $ ReplaceAt $ path [0, 0, 0])
                        [inside "two" [], Term.Node (Last $ ReplaceAt $ path [0, 1, 0]) [inside "two" []]]
            (atLeaves `elem` found, [map sitePathOf edits | Just edits <- map editsOfSet found])
                `shouldBe` ( True
                           ,
                               [ [path [0, 0, 0], path [0, 1, 0]]
                               , [path [0, 0], path [0, 1, 0]]
                               , [path [0, 0, 0], path [0, 1]]
                               , [path [0, 0], path [0, 1]]
                               , [path [0]]
                               , [path []]
                               ]
                           )
        it "gives no edit set for two equal terms" $
            editSetsBetween 2 expressions sum' sum' `shouldBe` Right []
        it "refuses a change with more candidate sets than the limit, with their number" $
            -- A complete binary tree of depth h has 1 + c(h - 1)^2 cuts: 2, 5, 26, 677, and 458330 for depth 5.
            editSetsBetween 32 trees (complete 5 "a") (complete 5 "b") `shouldBe` Left (TooManyCandidates 458330)
        it "gives the rank of each edit set in the generator of the automaton of edit sets, in rank order" $ do
            let sets = either (error . show) id $ editSetAutomaton 2 expressions twoSites
                generator = Gen.fromAutomaton $ fromFTA sets
                ranked = either (error . show) id $ rankedEditSetsBetween 2 expressions twoSites twoSitesNew
            sort (map snd ranked) `shouldBe` sort (either (error . show) id $ editSetsBetween 2 expressions twoSites twoSitesNew)
            map fst ranked `shouldBe` sort (map fst ranked)
            map (\(rank, _) -> Gen.unrank generator rank) ranked `shouldBe` map (Right . snd) ranked

-- | The largest edit size, minus one, that the tests compare.
bound :: Integer
bound = 5

-- | The largest new material of an edit set that the tests compare.
setBound :: Integer
setBound = 3

-- | The largest size of an edit set of at most k edits with the new material up to 'setBound'.
setLimit :: Int -> Integer
setLimit k = setBound + toInteger k

-- | The path of the site of an edit.
sitePathOf :: Edit String -> Path
sitePathOf (Term.Node site _) = sitePath site

-- | Binary trees over a and b.
trees :: FTA.PlainFTA String String
trees = fromRows "s" [("s", [leaf "a", leaf "b", node "g" ["s", "s"]])]

-- | The complete binary tree of a depth with the leaf at each place.
complete :: Int -> String -> Term String
complete depth leaf'
    | depth <= 0 = Term.Node leaf' []
    | otherwise = Term.Node "g" [complete (depth - 1) leaf', complete (depth - 1) leaf']

-- | New material of an edit set from its symbol and children.
inside :: String -> [Term (SetSymbol String)] -> Term (SetSymbol String)
inside = Term.Node . Inside . Material

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
