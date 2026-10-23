module Data.CFTA.InclusionSpec (spec) where

import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Inclusion
import Data.CFTA.Index (Size (..))
import Data.CFTA.Sized (sized, termsOfSize)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Inclusion" $ do
    it "agrees with a search of the size classes of the left automaton" $
        overPairs (inclusionUpTo bound) `shouldBe` overPairs (\left right -> Right $ search left right)
    it "gives a counterexample that the left automaton accepts, that the right rejects, and that no smaller term separates" $
        overPairs counterexampleCheck `shouldBe` overPairs (\left right -> Just $ smallestDifference left right)
    it "finds a missing tree at the first size where the languages differ, and not at rank zero" $ do
        -- The binary trees with five nodes are g(a, g(a, a)) and then
        -- g(g(a, a), a). The right combs have only the first.
        inclusionUpTo bound trees rightCombs
            `shouldBe` Right (NotIncluded $ term "g" [term "g" [term "a" [], term "a" []], term "a" []])
        inclusionUpTo bound rightCombs trees `shouldBe` Right (IncludedUpTo bound)
    it "finds a missing term that the runs of an ambiguous automaton would hide" $ do
        -- Counted by runs, both size classes have two members: f(a) and f(b)
        -- on the left, and f(a) twice in the intersection.
        inclusionUpTo bound fOfAOrB fOfATwice `shouldBe` Right (NotIncluded $ term "f" [term "b" []])
        inclusionUpTo bound fOfATwice fOfAOrB `shouldBe` Right (IncludedUpTo bound)
    it "makes an automaton equivalent to its trimmed and its reordered copies" $ do
        let copies = [("trimmed", inclusions (FTA.trim padded)), ("reordered", inclusions (reordered padded))]
            inclusions copy = (inclusionUpTo bound padded copy, inclusionUpTo bound copy padded)
        copies `shouldBe` [(name, (Right (IncludedUpTo bound), Right (IncludedUpTo bound))) | name <- ["trimmed", "reordered"]]
    it "gives the same counterexample for reordered copies of the two automata" $
        overPairs (\left right -> inclusionUpTo bound (reordered left) (reordered right))
            `shouldBe` overPairs (inclusionUpTo bound)
    it "rejects an automaton with a constraint" $ do
        let equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]
            pairs = automaton "s" [("s", [FTA.Transition (sym "g") ["q", "q"] equal]), ("q", [leaf "a", leaf "b"])]
        inclusionUpTo bound pairs trees `shouldBe` Left ConstrainedLeft
        inclusionUpTo bound trees pairs `shouldBe` Left ConstrainedRight
    it "includes every automaton up to a bound below one" $
        inclusionUpTo 0 treesOverAB trees `shouldBe` Right (IncludedUpTo 0)

-- | The largest size that the tests check.
bound :: Size
bound = 7

-- | The first term of the left automaton, by size and then by class rank, that the right automaton rejects.
search :: FTA.PlainFTA String Symbol -> FTA.PlainFTA String Symbol -> Inclusion Symbol
search left right =
    case [found | size <- [1 .. bound], found <- termsOfSize classes size, not (FTA.accepts right found)] of
        [] -> IncludedUpTo bound
        counterexample : _ -> NotIncluded counterexample
  where
    classes = either (error . show) id $ sized left

{- | Whether the left automaton accepts the counterexample and the right
automaton rejects it, with the size of the counterexample. 'Nothing' when the
counterexample fails, or for an error or 'Included'.
-}
counterexampleCheck :: FTA.PlainFTA String Symbol -> FTA.PlainFTA String Symbol -> Maybe (Maybe Size)
counterexampleCheck left right = case inclusionUpTo bound left right of
    Right (NotIncluded counterexample)
        | FTA.accepts left counterexample && not (FTA.accepts right counterexample) ->
            Just $ Just $ Size $ toInteger $ length counterexample
        | otherwise -> Nothing
    Right (IncludedUpTo _) -> Just Nothing
    _ -> Nothing

-- | The smallest size of a term over the alphabet that the left automaton accepts and the right rejects.
smallestDifference :: FTA.PlainFTA String Symbol -> FTA.PlainFTA String Symbol -> Maybe Size
smallestDifference left right =
    find
        (\size -> any (\candidate -> FTA.accepts left candidate && not (FTA.accepts right candidate)) (allTerms size))
        [1 .. bound]

-- | A function of each ordered pair of the fixtures, with the names of the pair.
overPairs :: (FTA.PlainFTA String Symbol -> FTA.PlainFTA String Symbol -> result) -> [(String, String, result)]
overPairs check = [(leftName, rightName, check left right) | (leftName, left) <- fixtures, (rightName, right) <- fixtures]

-- | The test automata, each with a name.
fixtures :: [(String, FTA.PlainFTA String Symbol)]
fixtures =
    [ ("binary trees", trees)
    , ("binary trees over a and b", treesOverAB)
    , ("right combs", rightCombs)
    , ("binary trees with a dead and an unreachable state", padded)
    ,
        ( "binary trees with two runs for some trees"
        , automaton "s" [("s", [leaf "a", node "g" ["s", "s"], node "g" ["l", "s"]]), ("l", [leaf "a"])]
        )
    , ("chains", automaton "s" [("s", [leaf "a", node "f" ["s"]])])
    , ("chains of even length", automaton "s" [("s", [leaf "a", node "f" ["o"]]), ("o", [node "f" ["s"]])])
    , ("f(a) or f(b)", fOfAOrB)
    , ("f(a), with two runs", fOfATwice)
    , ("the empty language", automaton "s" [("s", [])])
    ]

-- | Binary trees: a leaf, or a node with two trees.
trees :: FTA.PlainFTA String Symbol
trees = automaton "s" [("s", [leaf "a", node "g" ["s", "s"]])]

-- | Binary trees with two leaf symbols.
treesOverAB :: FTA.PlainFTA String Symbol
treesOverAB = automaton "s" [("s", [leaf "a", leaf "b", node "g" ["s", "s"]])]

-- | Binary trees whose left children are leaves.
rightCombs :: FTA.PlainFTA String Symbol
rightCombs = automaton "s" [("s", [leaf "a", node "g" ["l", "s"]]), ("l", [leaf "a"])]

-- | Binary trees, with a transition to a state that accepts nothing and a state that the initial state cannot reach.
padded :: FTA.PlainFTA String Symbol
padded =
    automaton
        "s"
        [ ("s", [node "f" ["dead"], leaf "a", node "g" ["s", "s"]])
        , ("dead", [node "f" ["dead"]])
        , ("unreachable", [leaf "b"])
        ]

-- | The terms f(a) and f(b), each with one run.
fOfAOrB :: FTA.PlainFTA String Symbol
fOfAOrB = automaton "s" [("s", [node "f" ["p"]]), ("p", [leaf "a", leaf "b"])]

-- | The term f(a), with two runs.
fOfATwice :: FTA.PlainFTA String Symbol
fOfATwice = automaton "s" [("s", [node "f" ["p"], node "f" ["q"]]), ("p", [leaf "a"]), ("q", [leaf "a"])]

-- | A copy with the states in the opposite order and each row reversed.
reordered :: FTA.PlainFTA String Symbol -> FTA.PlainFTA (Down String) Symbol
reordered original =
    FTA.mapStates Down
        $ either (error . show) id
        $ FTA.replaceRows (Map.map (Just . reverse) $ FTA.transitionTable original) original

-- | The symbols of the automata and their arities.
symbolArities :: [(String, Int)]
symbolArities = [("a", 0), ("b", 0), ("f", 1), ("g", 2)]

-- | Every term of the given size over the symbols of 'symbolArities'.
allTerms :: Size -> [Term Symbol]
allTerms size =
    [ term symbol children
    | (symbol, arity) <- symbolArities
    , children <- spread arity (size - 1)
    ]
  where
    spread 0 0 = [[]]
    spread 0 _ = []
    spread arity remaining =
        [ first : rest
        | firstSize <- [1 .. remaining - fromIntegral (arity - 1)]
        , first <- allTerms firstSize
        , rest <- spread (arity - 1) (remaining - firstSize)
        ]

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> FTA.PlainFTA String Symbol
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A transition without children.
leaf :: String -> FTA.Transition String Symbol Constraint
leaf symbol = FTA.Transition (sym symbol) [] noConstraint

-- | A transition without a constraint.
node :: String -> [String] -> FTA.Transition String Symbol Constraint
node symbol children = FTA.Transition (sym symbol) children noConstraint

-- | A symbol from its name.
sym :: String -> Symbol
sym = Symbol . Text.pack

-- | A term from its symbol name and children.
term :: String -> [Term Symbol] -> Term Symbol
term = Term.Node . sym
