module Data.CFTA.InclusionSpec (spec) where

import Control.Monad (filterM)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Ord (Down (..))
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (..), equalityConstraint, noConstraint, semanticConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Inclusion
import Data.CFTA.Index (Size (..))
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Expression (Formula, refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.Verdict (Entailment (Entailment), Verdict (..))
import Data.CFTA.Sized (sized, sizedUpTo, termsOfSize)
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Inclusion" $ do
    it "agrees with a search of the size classes of the left automaton" $
        overPairs boundedFixtures (inclusionUpTo bound)
            `shouldBe` overPairs boundedFixtures (\left right -> Right $ search left right)
    it "gives a counterexample that the left automaton accepts, that the right rejects, and that no smaller term separates" $
        overPairs boundedFixtures counterexampleCheck
            `shouldBe` overPairs boundedFixtures (\left right -> Just $ smallestDifference left right)
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
            inclusions copy =
                ( (inclusionUpTo bound padded copy, inclusionUpTo bound copy padded)
                , (inclusion padded copy, inclusion copy padded)
                )
        copies
            `shouldBe` [ (name, ((Right (IncludedUpTo bound), Right (IncludedUpTo bound)), (Right Included, Right Included)))
                       | name <- ["trimmed", "reordered"]
                       ]
    it "gives the same counterexample for reordered copies of the two automata" $ do
        overPairs boundedFixtures (\left right -> inclusionUpTo bound (reordered left) (reordered right))
            `shouldBe` overPairs boundedFixtures (inclusionUpTo bound)
        overPairs fixtures (\left right -> inclusion (reordered left) (reordered right)) `shouldBe` overPairs fixtures inclusion
    it "decides equality constraints" $ do
        inclusionUpTo bound equalPairs pairsOfChains `shouldBe` Right (IncludedUpTo bound)
        inclusionUpTo bound pairsOfChains equalPairs `shouldBe` Right (NotIncluded $ term "g" [term "a" [], term "b" []])
        inclusionUpTo bound chainAndItsF equalPairs
            `shouldBe` Right (NotIncluded $ term "g" [term "f" [term "a" []], term "a" []])
        -- The same equality, at the transition of g or at the root, two
        -- levels above the equal chains.
        (inclusionUpTo bound fOfEqualPairs fOfEqualPairsAtRoot, inclusionUpTo bound fOfEqualPairsAtRoot fOfEqualPairs)
            `shouldBe` (Right (IncludedUpTo bound), Right (IncludedUpTo bound))
    it "rejects an automaton with a constraint that the check does not decide" $ do
        let different = semanticConstraint $ Not $ Same (ECTA.path [0]) (ECTA.path [1])
            differentPairs = automaton "s" $ ("s", [FTA.Transition (sym "g") ["t", "t"] different]) : chainRows "t"
        inclusionUpTo bound differentPairs trees `shouldBe` Left ConstrainedLeft
        inclusionUpTo bound trees differentPairs `shouldBe` Left ConstrainedRight
        inclusion equalPairs trees `shouldBe` Left ConstrainedLeft
        inclusion trees equalPairs `shouldBe` Left ConstrainedRight
    it "includes every automaton up to a bound below one" $
        inclusionUpTo 0 treesOverAB trees `shouldBe` Right (IncludedUpTo 0)
    it "agrees with the bounded check on every pair" $
        -- The largest smallest counterexample of a pair has five nodes, so
        -- the bound shows each counterexample.
        overPairs fixtures (\left right -> upToBound <$> inclusion left right)
            `shouldBe` overPairs fixtures (inclusionUpTo bound)
    it "shows the inclusion of two infinite languages, which no bound shows" $ do
        inclusion chainsBySix evenChains `shouldBe` Right Included
        inclusionUpTo bound chainsBySix evenChains `shouldBe` Right (IncludedUpTo bound)
        (inclusion evenChains evenChainsByFour, inclusion evenChainsByFour evenChains)
            `shouldBe` (Right Included, Right Included)
        inclusion evenChains chainsBySix `shouldBe` Right (NotIncluded $ chain 2)
    it "finds the smallest counterexample above the bound of the other tests" $ do
        -- The lengths 0, 3, 6, 9, and so on, against the lengths 0, 3, 6, 12,
        -- 18, and so on: the chain of length 9 is missing.
        let byThree = automaton "d0" [("d0", [leaf "a", node "f" ["d2"]]), ("d1", [node "f" ["d0"]]), ("d2", [node "f" ["d1"]])]
            bySixOrThree =
                automaton "s" $
                    ("s", [leaf "a", node "f" ["c5"], node "f" ["t2"]])
                        : ("t0", [leaf "a"])
                        : [("t" <> show length', [node "f" ["t" <> show (length' - 1)]]) | length' <- [1 .. 2 :: Int]]
                            <> sixRows
        inclusion byThree bySixOrThree `shouldBe` Right (NotIncluded $ chain 9)
        inclusion byThree bySixOrThree `shouldBe` inclusionUpTo 20 byThree bySixOrThree
    describe "with a solver" $ do
        it "agrees with the check without a solver where no guard needs one" $ do
            found <-
                traverse (\(leftName, rightName, check) -> (leftName,rightName,) . Right <$> check) $
                    overPairs boundedFixtures (inclusionUpToWith unusedEntailment bound)
            found `shouldBe` overPairs boundedFixtures (inclusionUpTo bound)
        it "agrees with a search of the size classes of the left automaton, with the solver" $ do
            found <-
                traverse (\(leftName, rightName, check) -> (leftName,rightName,) <$> check) $
                    overPairs guardFixtures (inclusionUpToWith partialEntailment bound)
            expected <-
                traverse (\(leftName, rightName, check) -> (leftName,rightName,) <$> check) $
                    overPairs guardFixtures solverSearch
            found `shouldBe` expected
        it "makes a guard on both children equivalent to a smaller set of leaves" $ do
            found <- traverse (uncurry $ inclusionUpToWith partialEntailment bound) [(bothAboveOne, twos), (twos, bothAboveOne)]
            found `shouldBe` [IncludedUpTo bound, IncludedUpTo bound]
        it "stops at the first size with a guard that the solver does not decide" $ do
            -- The guard of the right automaton on g(n3, x) is not decided. A
            -- term with three nodes is the smallest term.
            stopped <-
                inclusionUpToWith partialEntailment bound (numberPairs [1, 2, 3] noConstraint) (numberPairs [1, 2, 3] firstAboveOne)
            stopped `shouldBe` UnknownAt 3
            belowStop <-
                inclusionUpToWith partialEntailment 2 (numberPairs [1, 2, 3] noConstraint) (numberPairs [1, 2, 3] firstAboveOne)
            belowStop `shouldBe` IncludedUpTo 2
        it "gives a counterexample below a guard that the solver does not decide" $ do
            let withLeaf = automaton "s" [("s", [leaf "m", node "g" ["q", "q"]]), ("q", map number [1, 2, 3])]
            found <- inclusionUpToWith partialEntailment bound withLeaf (numberPairs [1, 2, 3] firstAboveOne)
            found `shouldBe` NotIncluded (term "m" [])
        it "stops at a guard of the left automaton that the solver does not decide" $ do
            stopped <-
                inclusionUpToWith partialEntailment bound (numberPairs [1, 3] firstAboveOne) (numberPairs [1, 2, 3] noConstraint)
            stopped `shouldBe` UnknownAt 3

-- | The largest size that the tests check.
bound :: Size
bound = 7

-- | The result of an exact check as the bounded check up to 'bound' gives it.
upToBound :: Inclusion Symbol -> Inclusion Symbol
upToBound Included = IncludedUpTo bound
upToBound other = other

{- | The first term of the left automaton, by size and then by class rank,
that the right automaton does not accept with 'partialEntailment'. The classes
come from 'sizedUpTo', and the acceptance from 'FTA.acceptsM'.
-}
solverSearch :: FTA.PlainFTA String Symbol -> FTA.PlainFTA String Symbol -> IO (Inclusion Symbol)
solverSearch left right = do
    classes <- sizedUpTo partialEntailment bound left >>= either (fail . show) pure
    missing <- filterM (fmap not . acceptedByRight) [found | size <- [1 .. bound], found <- termsOfSize classes size]
    pure $ maybe (IncludedUpTo bound) NotIncluded $ listToMaybe missing
  where
    acceptedByRight = FTA.acceptsM decide right
    decide _ transition candidate = (== Yes) <$> evaluateConstraint partialEntailment (FTA.transitionConstraint transition) candidate

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

-- | A function of each ordered pair of some fixtures, with the names of the pair.
overPairs ::
    [(String, FTA.PlainFTA String Symbol)] ->
    (FTA.PlainFTA String Symbol -> FTA.PlainFTA String Symbol -> result) ->
    [(String, String, result)]
overPairs named check = [(leftName, rightName, check left right) | (leftName, left) <- named, (rightName, right) <- named]

-- | The fixtures of the bounded check: those without constraints and those with equality constraints.
boundedFixtures :: [(String, FTA.PlainFTA String Symbol)]
boundedFixtures = fixtures <> equalityFixtures

-- | The test automata with equality constraints, each with a name, and the chains they compare.
equalityFixtures :: [(String, FTA.PlainFTA String Symbol)]
equalityFixtures =
    [ ("pairs of chains", pairsOfChains)
    , ("pairs of equal chains", equalPairs)
    ,
        ( "pairs of equal chains, from two states"
        , automaton "s" $ ("s", [equalAt "g" ["t", "u"] [0] [1]]) : chainRows "t" <> chainRows "u"
        )
    , ("f of pairs of equal chains", fOfEqualPairs)
    , ("f of pairs of equal chains, with the equality at the root", fOfEqualPairsAtRoot)
    , ("g(f(x), x)", chainAndItsF)
    ]

-- | The pairs g(x, y) of chains x and y over a and b.
pairsOfChains :: FTA.PlainFTA String Symbol
pairsOfChains = automaton "s" $ ("s", [node "g" ["t", "t"]]) : chainRows "t"

-- | The pairs g(x, x) of equal chains over a and b.
equalPairs :: FTA.PlainFTA String Symbol
equalPairs = automaton "s" $ ("s", [equalAt "g" ["t", "t"] [0] [1]]) : chainRows "t"

-- | The terms f(g(x, x)), with the equality on the transition of g.
fOfEqualPairs :: FTA.PlainFTA String Symbol
fOfEqualPairs = automaton "s" $ ("s", [node "f" ["p"]]) : ("p", [equalAt "g" ["t", "t"] [0] [1]]) : chainRows "t"

-- | The terms f(g(x, x)), with the equality on the transition of f.
fOfEqualPairsAtRoot :: FTA.PlainFTA String Symbol
fOfEqualPairsAtRoot = automaton "s" $ ("s", [equalAt "f" ["p"] [0, 0] [0, 1]]) : ("p", [node "g" ["t", "t"]]) : chainRows "t"

-- | The terms g(f(x), x) of a chain x over a and b.
chainAndItsF :: FTA.PlainFTA String Symbol
chainAndItsF = automaton "s" $ ("s", [equalAt "g" ["t", "t"] [0, 0] [1]]) : chainRows "t"

-- | A state of the chains over a and b.
chainRows :: String -> [(String, [FTA.Transition String Symbol Constraint])]
chainRows state = [(state, [leaf "a", leaf "b", node "f" [state]])]

-- | A transition whose subterms at the two paths are equal.
equalAt :: String -> [String] -> [ECTA.ChildIndex] -> [ECTA.ChildIndex] -> FTA.Transition String Symbol Constraint
equalAt symbol children one other =
    FTA.Transition (sym symbol) children $ equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path one, ECTA.path other]]

-- | Pairs of refined leaves, with guards that 'partialEntailment' decides, each with a name.
guardFixtures :: [(String, FTA.PlainFTA String Symbol)]
guardFixtures =
    [ ("pairs of 1 and 2", numberPairs [1, 2] noConstraint)
    , ("pairs of 1 and 2, the first above one", numberPairs [1, 2] firstAboveOne)
    , ("pairs of 1 and 2, the second above one", numberPairs [1, 2] $ semanticConstraint $ Satisfies (ECTA.path [1]) aboveOne)
    , ("pairs of 1 and 2, both above one", bothAboveOne)
    , ("pairs of 2", twos)
    ]

-- | The pairs g(x, y) of leaves with the given numbers, with a constraint on g.
numberPairs :: [Integer] -> Constraint -> FTA.PlainFTA String Symbol
numberPairs numbers constraint = automaton "s" [("s", [FTA.Transition (sym "g") ["q", "q"] constraint]), ("q", map number numbers)]

-- | The pairs of 1 and 2 whose two children are above one.
bothAboveOne :: FTA.PlainFTA String Symbol
bothAboveOne =
    numberPairs [1, 2] $ semanticConstraint $ And [Satisfies (ECTA.path [0]) aboveOne, Satisfies (ECTA.path [1]) aboveOne]

-- | The pair of 2 and 2, without a guard.
twos :: FTA.PlainFTA String Symbol
twos = numberPairs [2] noConstraint

-- | The guard that the first child is above one.
firstAboveOne :: Constraint
firstAboveOne = semanticConstraint $ Satisfies (ECTA.path [0]) aboveOne

-- | A leaf n with the refinement that its value is the number.
number :: Integer -> FTA.Transition String Symbol Constraint
number value = FTA.Transition (RefinedSymbol (sym "n") (valueIs value)) [] noConstraint

-- | The refinement that the value is the number.
valueIs :: Integer -> Formula
valueIs value = refinementFormula (.== fromInteger value)

-- | The refinement that the value is above one.
aboveOne :: Formula
aboveOne = refinementFormula (.> 1)

{- | A solver that decides only whether the values 1 and 2 are above one. It
does not decide the value 3, or any other question.
-}
partialEntailment :: Entailment
partialEntailment = Entailment $ \antecedent consequent ->
    pure $
        if consequent /= aboveOne
            then Unknown
            else
                if antecedent == valueIs 2
                    then Yes
                    else if antecedent == valueIs 1 then No else Unknown

-- | A solver that fails the test when the check calls it.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> fail "unexpected solver call"

-- | The test automata without constraints, each with a name.
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
    , ("chains of even length", evenChains)
    , ("chains of even length, by residues modulo four", evenChainsByFour)
    , ("chains with a length divisible by six", chainsBySix)
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

-- | The chains f(...f(a)) with an even number of f nodes.
evenChains :: FTA.PlainFTA String Symbol
evenChains = automaton "s" [("s", [leaf "a", node "f" ["o"]]), ("o", [node "f" ["s"]])]

{- | The chains with an even number of f nodes, as the union of the lengths 0
and 2 modulo 4. The state r accepts the lengths that are k modulo 4.
-}
evenChainsByFour :: FTA.PlainFTA String Symbol
evenChainsByFour =
    automaton
        "s"
        [ ("s", [leaf "a", node "f" ["r3"], node "f" ["r1"]])
        , ("r0", [leaf "a", node "f" ["r3"]])
        , ("r1", [node "f" ["r0"]])
        , ("r2", [node "f" ["r1"]])
        , ("r3", [node "f" ["r2"]])
        ]

-- | The chains whose number of f nodes is divisible by six.
chainsBySix :: FTA.PlainFTA String Symbol
chainsBySix = automaton "c0" sixRows

-- | The rows of 'chainsBySix'. The state ck accepts the lengths that are k modulo 6.
sixRows :: [(String, [FTA.Transition String Symbol Constraint])]
sixRows = ("c0", [leaf "a", node "f" ["c5"]]) : [("c" <> show k, [node "f" ["c" <> show (k - 1)]]) | k <- [1 .. 5 :: Int]]

-- | The chain with the given number of f nodes.
chain :: Int -> Term Symbol
chain length' = iterate (\below -> term "f" [below]) (term "a" []) !! length'

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
