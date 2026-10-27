module Data.CFTA.EditSpec (spec) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (sort)
import Data.Maybe (listToMaybe)
import qualified Data.Map.Strict as Map
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import Data.CFTA.Edit
import qualified Data.CFTA.Equality as ECTA
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (ChildIndex (..), Size (..), TransitionIndex (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Path (path)
import Data.CFTA.Sized (countOfSize, sized, termsOfSize)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Edit" $ do
    it "has one run for each edit, so the generator counts the edits as the size classes do" $
        [ ( name
          , [found | size <- [1 .. bound + 1], found <- termsOfSize classes (Size size), runs edits found /= 1]
          , generatorCounts
          )
        | (name, automaton, given) <- fixtures
        , let edits = editsOf automaton given
              classes = either (error . show) id $ sized edits
              generator = Gen.fromAutomaton $ fromFTA edits
              generatorCounts = and [Gen.countAtSize generator (Size size) == Right (countOfSize classes (Size size)) | size <- [1 .. bound + 1]]
        ]
            `shouldBe` [(name, [], True) | (name, _, _) <- fixtures]
    it "gives each edited term, with the size of the edit, as often as the definition does" $
        [ ( name
          , Map.fromListWith
                (+)
                [ ((edited, fromInteger size), 1 :: Int)
                | size <- [1 .. bound + 1]
                , edit <- termsOfSize classes (Size size)
                , Just edited <- [applyEdit given edit]
                , length edited <= fromInteger bound
                ]
          )
        | (name, automaton, given) <- fixtures
        , let classes = either (error . show) id $ sized $ editsOf automaton given
        ]
            `shouldBe` [ ( name
                         , Map.fromList
                            [ ((edited, size), count)
                            | edited <- allTerms automaton =<< [1 .. fromInteger bound]
                            , let costs = editCosts automaton given edited
                            , size <- nubOrd costs
                            , let count = length (filter (== size) costs)
                            ]
                         )
                       | (name, automaton, given) <- fixtures
                       ]
    it "gives the edits with the least new material first" $
        -- Each position of state e can be wrapped in neg, with no new material. An unwrap has none either.
        sort (termsOfSize (either (error . show) id $ sized $ editsOf expressions sum') 1)
            `shouldBe` sort
                ( [term (WrapAt (path at) "neg" 1 0) [] | at <- [[], [0], [1], [1, 0]]]
                    <> [term (UnwrapAt (path at) (ChildIndex index)) [] | (at, index) <- [([], 0), ([], 1), ([1], 0)]]
                )
    it "applies an edit" $ do
        applyEdit sum' (term (ReplaceAt $ path [1, 0]) [material "lit" [material "one" []]])
            `shouldBe` Just (Term.Node "add" [lit "one", Term.Node "neg" [lit "one"]])
        applyEdit sum' (term (WrapAt (path [0]) "add" (TransitionIndex 2) (ChildIndex 1)) [material "lit" [material "two" []]])
            `shouldBe` Just (Term.Node "add" [Term.Node "add" [lit "two", lit "one"], Term.Node "neg" [lit "two"]])
        applyEdit sum' (term (ReplaceAt $ path [2]) [material "one" []]) `shouldBe` Nothing
        applyEdit sum' (term (ReplaceAt $ path []) [term (ReplaceAt $ path []) []]) `shouldBe` Nothing
    describe "unwraps and context wraps" $ do
        it "does not unwrap to a child that the state does not accept" $
            -- A body has a cons only, so cons(skip, nil) is not a body that nil replaces.
            [ edit | edit@(Term.Node (UnwrapAt _ _) _) <- termsOfSize (either (error . show) id $ sized $ editsOf statements block) 1
            ]
                `shouldBe` []
        it "unwraps a statement of a list" $
            applyEdit blocks (term (UnwrapAt (path [0, 1]) (ChildIndex 1)) []) `shouldBe` Just block
        it "wraps a statement in an if, with the hole two nodes below" $ do
            applyEdit
                block
                ( term
                    (ContextAt (path [0, 0]) "if" (TransitionIndex 0) (ChildIndex 0))
                    [term (HoleParent "cons" (ChildIndex 0)) [material "nil" []]]
                )
                `shouldBe` Just
                    ( Term.Node
                        "block"
                        [Term.Node "cons" [Term.Node "if" [Term.Node "cons" [Term.Node "skip" [], Term.Node "nil" []]], Term.Node "nil" []]]
                    )
            -- The other context wrap of this size wraps the body: cons(if(hole), nil).
            (length . filter isContext) (termsOfSize (either (error . show) id $ sized $ editsOf statements block) 3) `shouldBe` 2
        it "gives a statement edit the size of its new nodes" $ do
            let skip = Term.Node "skip" []
                nil = Term.Node "nil" []
                cons = Term.Node "cons"
                smallest target =
                    listToMaybe
                        [ size
                        | size <- [1 .. 4]
                        , edit <- termsOfSize (either (error . show) id $ sized $ editsOf statements blocks) (Size size)
                        , applyEdit blocks edit == Just (Term.Node "block" [target])
                        ]
            -- Delete the second statement, insert a statement before it, and wrap the first in an if.
            smallest (cons [skip, nil]) `shouldBe` Just 1
            smallest (cons [skip, cons [skip, cons [skip, nil]]]) `shouldBe` Just 2
            smallest (cons [Term.Node "if" [cons [skip, nil]], cons [skip, nil]]) `shouldBe` Just 3
        it "refuses an edit with two holes or none" $ do
            applyEdit
                block
                ( term
                    (ContextAt (path [0, 0]) "if" (TransitionIndex 0) (ChildIndex 0))
                    [material "cons" [material "skip" [], material "nil" []]]
                )
                `shouldBe` Nothing
            applyEdit
                block
                ( term
                    (ContextAt (path [0, 0]) "if" (TransitionIndex 0) (ChildIndex 0))
                    [term (HoleParent "cons" (ChildIndex 0)) [term (HoleParent "cons" (ChildIndex 0)) []]]
                )
                `shouldBe` Nothing
    describe "rejects" $ do
        it "an automaton with a constraint" $ do
            let equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]
            editError (fromRows "s" [("s", [leaf "a", FTA.Transition "g" ["s", "s"] equal])]) (Term.Node "a" [])
                `shouldBe` Just ConstrainedAutomaton
        it "a term that the automaton does not accept" $
            editError expressions (Term.Node "one" []) `shouldBe` Just NotAccepted
        it "a term with two runs" $
            editError
                (fromRows "s" [("s", [leaf "a", node "f" ["s"], node "f" ["p"]]), ("p", [leaf "a"])])
                (Term.Node "f" [Term.Node "a" []])
                `shouldBe` Just SeveralRuns

-- | The largest edited term that the tests check.
bound :: Integer
bound = 6

-- | The fixtures: an unambiguous automaton and a term that it accepts.
fixtures :: [(String, FTA.PlainFTA String String, Term String)]
fixtures =
    [ ("expressions", expressions, sum')
    , ("chains", fromRows "s" [("s", [leaf "a", node "f" ["s"]])], Term.Node "f" [Term.Node "f" [Term.Node "a" []]])
    ,
        ( "binary trees over a and b"
        , fromRows "s" [("s", [leaf "a", leaf "b", node "g" ["s", "s"]])]
        , Term.Node "g" [Term.Node "a" [], Term.Node "g" [Term.Node "b" [], Term.Node "a" []]]
        )
    , ("statements", statements, blocks)
    ,
        ( "pairs with a flag on either side"
        , fromRows
            "e"
            [ ("e", [node "num" ["n"], node "pair" ["e", "b"], node "pair" ["b", "e"]])
            , ("n", [leaf "one", leaf "two"])
            , ("b", [leaf "yes", leaf "no"])
            ]
        , Term.Node "pair" [Term.Node "num" [Term.Node "one" []], Term.Node "yes" []]
        )
    ]

-- | Expressions: a literal of a number, a negation, or a sum.
expressions :: FTA.PlainFTA String String
expressions = fromRows "e" [("e", [node "lit" ["n"], node "neg" ["e"], node "add" ["e", "e"]]), ("n", [leaf "one", leaf "two"])]

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

-- | A block of one statement.
block :: Term String
block = Term.Node "block" [Term.Node "cons" [Term.Node "skip" [], Term.Node "nil" []]]

-- | A block of two statements.
blocks :: Term String
blocks =
    Term.Node "block" [Term.Node "cons" [Term.Node "skip" [], Term.Node "cons" [Term.Node "skip" [], Term.Node "nil" []]]]

-- | Whether an edit is a context wrap.
isContext :: Edit String -> Bool
isContext (Term.Node (ContextAt{}) _) = True
isContext _ = False

-- | The sum add(lit(one), neg(lit(two))).
sum' :: Term String
sum' = Term.Node "add" [lit "one", Term.Node "neg" [lit "two"]]

-- | A literal of a number.
lit :: String -> Term String
lit number = Term.Node "lit" [Term.Node number []]

-- | The edit automaton of a fixture.
editsOf :: FTA.PlainFTA String String -> Term String -> FTA.PlainFTA (EditState String String) (EditSymbol String)
editsOf automaton given = either (error . show) id $ editAutomaton automaton given

-- | The error of an edit automaton, if any.
editError :: FTA.PlainFTA String String -> Term String -> Maybe EditError
editError automaton given = either Just (const Nothing) $ editAutomaton automaton given

{- | The sizes of the edits that give the candidate from the given term, by the
definition: replacements of a subterm by another term of the state of its
position, wraps and context wraps of a subterm in a term of the state of its
position, and unwraps of a subterm to a child that the state accepts.
-}
editCosts :: FTA.PlainFTA String String -> Term String -> Term String -> [Int]
editCosts automaton given candidate = replacements <> wraps <> contexts <> unwraps
  where
    places =
        [ (at, state, old, new)
        | at <- positions given
        , agreesOutside at
        , Just old <- [subtermAt given at]
        , Just new <- [subtermAt candidate at]
        , state <- runStates at
        ]
    replacements = [1 + length new | (_, state, old, new) <- places, new /= old, acceptsAt state new]
    wraps =
        [ length candidateNode - length old
        | (_, state, old, candidateNode@(Term.Node symbol arguments)) <- places
        , FTA.Transition other children _ <- FTA.transitionsFrom automaton state
        , other == symbol
        , length children == length arguments
        , (hole, child) <- zip [0 :: Int ..] children
        , arguments !! hole == old
        , acceptsAt child old
        , and [acceptsAt sibling argument | (other', (sibling, argument)) <- zip [0 ..] (zip children arguments), other' /= hole]
        ]
    -- A context wrap puts the old subterm deeper than the children of the new node.
    contexts =
        [ length new - length old
        | (_, state, old, new) <- places
        , acceptsAt state new
        , deeper <- positions new
        , length deeper >= 2
        , subtermAt new deeper == Just old
        ]
    -- An unwrap replaces the subterm by a child that the state accepts.
    unwraps =
        [ 1
        | (_, state, Term.Node _ children, new) <- places
        , child <- children
        , child == new
        , acceptsAt state new
        ]
    agreesOutside at = (replaceAt candidate at =<< subtermAt given at) == Just given
    -- A state is a run state of a position when it accepts the subterm there,
    -- and the term with a hole there, which only the state accepts, is accepted.
    runStates at =
        [ state
        | state <- FTA.states automaton
        , Just old <- [subtermAt given at]
        , acceptsAt state old
        , Just holed <- [replaceAt given at (Term.Node "hole" [])]
        , FTA.accepts (withHole state) holed
        ]
    withHole state = fromRows (FTA.initialState automaton) $ (state, [leaf "hole"]) : Map.toList (FTA.transitionTable automaton)
    acceptsAt state = FTA.accepts (rooted Map.! state)
    rooted = Map.fromList [(state, fromRows state $ Map.toList $ FTA.transitionTable automaton) | state <- FTA.states automaton]

-- | The number of runs of an automaton on a term.
runs :: (Ord state, Eq symbol) => FTA.PlainFTA state symbol -> Term symbol -> Integer
runs automaton = go (FTA.initialState automaton)
  where
    go state (Term.Node symbol children) =
        sum
            [ product (zipWith go childStates children)
            | FTA.Transition other childStates _ <- FTA.transitionsFrom automaton state
            , other == symbol
            , length childStates == length children
            ]

-- | The positions of a term, the root first.
positions :: Term String -> [[Int]]
positions (Term.Node _ children) = [] : [index : at | (index, child) <- zip [0 ..] children, at <- positions child]

-- | The subterm at a position.
subtermAt :: Term String -> [Int] -> Maybe (Term String)
subtermAt found [] = Just found
subtermAt (Term.Node _ children) (index : rest) = case drop index children of
    child : _ -> subtermAt child rest
    [] -> Nothing

-- | The term with the subterm at a position replaced.
replaceAt :: Term String -> [Int] -> Term String -> Maybe (Term String)
replaceAt _ [] new = Just new
replaceAt (Term.Node symbol children) (index : rest) new = case splitAt index children of
    (before, child : after) -> (\changed -> Term.Node symbol (before <> (changed : after))) <$> replaceAt child rest new
    _ -> Nothing

-- | Every term of the given size over the symbols of the automaton.
allTerms :: FTA.PlainFTA String String -> Int -> [Term String]
allTerms automaton = go
  where
    symbols =
        nubOrd
            [ (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
            | transitions <- Map.elems $ FTA.transitionTable automaton
            , transition <- transitions
            ]
    go size = [Term.Node symbol children | (symbol, arity) <- symbols, children <- spread arity (size - 1)]
    spread 0 0 = [[]]
    spread 0 _ = []
    spread arity remaining =
        [ first : rest
        | firstSize <- [1 .. remaining - (arity - 1)]
        , first <- go firstSize
        , rest <- spread (arity - 1) (remaining - firstSize)
        ]

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
