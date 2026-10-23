module Data.CFTA.SizedSpec (spec) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck (Property, counterexample, (.&&.), (===))
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (..), equalityConstraint, noConstraint, semanticConstraint)
import Data.CFTA.Equality (numNestedMu)
import qualified Data.CFTA.Equality as ECTA
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Reference (Automaton (..), AutomatonEdge (..), automatonNode, closedAutomaton)
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size (..))
import Data.CFTA.Interned (toFTA)
import Data.CFTA.Refinement (Entailment (Entailment))
import Data.CFTA.Sized
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Sized" $ do
    it "lists the classes of a recursion with an empty class between two others" $ do
        let classes = fromRows "s" [("s", [leaf "a", node "g" ["s", "s"]])]
        map (countOfSize classes) [1 .. 5] `shouldBe` [1, 0, 1, 0, 2]
        termsOfSize classes 3 `shouldBe` [term "g" [term "a" [], term "a" []]]
    it "counts and ranks a large class with the count table" $ do
        let classes = fromRows "s" [("s", [leaf "a", node "g" ["s", "s"]])]
            rank = ClassRank 4000000000
        -- The binary trees with 20 inner nodes: the Catalan number C(20).
        countOfSize classes 41 `shouldBe` 6564120420
        fmap (rankOfSize classes) (unrankOfSize classes 41 rank) `shouldBe` Just (Just (41, rank))
    it "keeps the order of the rows with a dead transition" $ do
        -- With the count table, an interned import dropped a(dead) and so
        -- changed the classes that order the transitions of s.
        let rows =
                [ ("s", [node "f" ["p"], node "f" ["q"]])
                , ("p", [node "a" ["dead"], node "z" ["leaf"]])
                , ("q", [node "m" ["leaf"]])
                , ("leaf", [leaf "k"])
                , ("dead", [])
                ]
        termsOfSize (fromRows "s" rows) 3 `shouldBe` termsOfSize (fromReference "s" rows) 3
    it "keeps the order of the rows with a repeated transition" $ do
        -- An interned import merged the two a transitions of p.
        let rows =
                [ ("s", [node "f" ["p", "r"], node "f" ["q", "t"]])
                , ("p", [leaf "a", leaf "a", leaf "z"])
                , ("q", [leaf "a", leaf "m"])
                , ("r", [leaf "r"])
                , ("t", [leaf "t"])
                ]
        termsOfSize (fromRows "s" rows) 3 `shouldBe` termsOfSize (fromReference "s" rows) 3
    it "lists a term that two transitions accept once" $ do
        let classes = fromRows "s" [("s", [node "f" ["p"], node "f" ["q"]]), ("p", [leaf "a"]), ("q", [leaf "a"])]
        termsOfSize classes 2 `shouldBe` [term "f" [term "a" []]]
    it "checks the equality constraints of a transition" $ do
        let equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]
            classes = fromRows "s" [("s", [FTA.Transition (sym "g") ["q", "q"] equal]), ("q", [leaf "a", leaf "b"])]
        termsOfSize classes 3 `shouldBe` [term "g" [term "a" [], term "a" []], term "g" [term "b" [], term "b" []]]
    it "rejects a guard beyond equality constraints" $ do
        let different = semanticConstraint $ Not $ Same (ECTA.path [0]) (ECTA.path [1])
            rows = [("s", [FTA.Transition (sym "g") ["q", "q"] different]), ("q", [leaf "a", leaf "b"])]
        either Just (const Nothing) (sized $ automaton "s" rows) `shouldBe` Just ResidualGuard
    modifyMaxSuccess (const 300) $ do
        it "lists each accepted term of each size once, and ranks it" $ QC.property exactClasses
        it "agrees with the cyclic import wherever the import accepts the automaton" $ QC.property importAgreement
        it "gives the sequence of the reference, also where it uses the count table" $ QC.property referenceAgreement
        it "decides the classes up to a bound as the reference builds them" $ QC.property boundedAgreement

-- | The classes of size one to 'sizeBound' are the accepted terms of each size, each once, and the ranks invert.
exactClasses :: SizedAutomaton -> Property
exactClasses (SizedAutomaton description) =
    counterexample (show description)
        $ QC.within 5000000
        $ QC.conjoin
            [ counterexample ("size " <> show size) $
                sort found === sort expected
                    .&&. length (nubOrd found) === length found
                    .&&. countOfSize classes (Size size) === Cardinality (toInteger $ length found)
                    .&&. QC.conjoin
                        [ unrankOfSize classes (Size size) (ClassRank rank) === Just found'
                            .&&. rankOfSize classes found' === Just (Size size, ClassRank rank)
                        | (rank, found') <- zip [0 ..] found
                        ]
                    .&&. unrankOfSize classes (Size size) (ClassRank $ toInteger $ length found) === Nothing
                    .&&. QC.conjoin
                        [ termsOfSizeFrom classes (Size size) (ClassRank $ toInteger from) === drop from found
                        | from <- [-1 .. length found + 1]
                        ]
            | size <- [1 .. sizeBound]
            , let found = termsOfSize classes (Size size)
            , let expected = filter (FTA.accepts graph) (allTerms size)
            ]
  where
    graph = either (error . show) id $ toFTA $ automatonNode description
    classes = either (error . show) id $ sized graph

{- | The cyclic import counts, unranks, and ranks the terms of each size as the
reference does, when it accepts the automaton.
-}
importAgreement :: SizedAutomaton -> Property
importAgreement (SizedAutomaton description) =
    counterexample (show description) $
        QC.tabulate "import" [outcome] $
            QC.within 5000000 $
                -- An acyclic automaton has the finite import, whose sizes differ.
                case Gen.countAtSize generator 1 of
                    Right _
                        | numNestedMu root > 0 ->
                            QC.conjoin
                                [ counterexample ("size " <> show size) $
                                    Gen.countAtSize generator (Size size) === Right (countOfSize classes (Size size))
                                        .&&. QC.conjoin
                                            [ Gen.unrank generator (Rank $ offset + rank) === Right found
                                            | (rank, found) <- zip [0 ..] $ termsOfSize classes (Size size)
                                            ]
                                | size <- [1 .. sizeBound]
                                , let offset = sum [count | smaller <- [1 .. size - 1], let Cardinality count = countOfSize classes (Size smaller)]
                                ]
                    _ -> QC.property True
  where
    outcome
        | numNestedMu root == 0 = "acyclic"
        | otherwise = either (takeWhile (/= ' ') . show) (const "cyclic, accepted") (Gen.countAtSize generator 1)
    root = automatonNode description
    generator = Gen.fromAutomaton root
    classes = either (error . show) id $ sized $ either (error . show) id $ toFTA root

{- | 'sized' gives the classes of 'sizedReference', in the same order, also
with a dead or a repeated transition in every other row. An interned import would
drop both, so they check that the count table reads the original rows.
-}
referenceAgreement :: SizedAutomaton -> Property
referenceAgreement (SizedAutomaton description) =
    counterexample (show description)
        $ QC.within 5000000
        $ QC.conjoin
            [ counterexample (label <> ", size " <> show size) $
                termsOfSize classes (Size size) === termsOfSize reference (Size size)
                    .&&. countOfSize classes (Size size) === countOfSize reference (Size size)
            | (label, extra) <-
                [("as built", const []), ("with a dead transition", const [dead]), ("with a repeated transition", take 1)]
            , let padded = withExtra extra
                  classes = either (error . show) id $ sized padded
                  reference = either (error . show) id $ sizedReference padded
            , size <- [1 .. sizeBound]
            ]
  where
    graph = either (error . show) id $ toFTA $ automatonNode description
    dead = FTA.Transition (sym "f") [Nothing] noConstraint
    -- Every other row of the graph with the extra transitions, and a dead
    -- state, so that the rows compare differently once an interned import
    -- drops the extra transitions.
    withExtra extra =
        either (error . show) id
            $ FTA.mkFTA (Just $ FTA.initialState graph)
            $ (Nothing, [])
                : [ (Just state, if even position then transitions <> extra transitions else transitions)
                  | (position, (state, original)) <- zip [0 :: Int ..] $ Map.toList (FTA.transitionTable graph)
                  , let transitions = [transition{FTA.transitionChildren = map Just (FTA.transitionChildren transition)} | transition <- original]
                  ]

{- | 'sizedUpTo' decides equality constraints without the solver and gives the
classes of 'sizedReference' up to its bound, and no term above it.
-}
boundedAgreement :: SizedAutomaton -> Property
boundedAgreement (SizedAutomaton description) = QC.ioProperty $ do
    decided <- sizedUpTo unusedEntailment (Size bound) graph
    pure $
        counterexample (show description) $ case decided of
            Left err -> counterexample (show err) False
            Right classes ->
                QC.conjoin
                    [ counterexample ("size " <> show size) $
                        termsOfSize classes (Size size) === if size <= bound then termsOfSize reference (Size size) else []
                    | size <- [1 .. sizeBound]
                    ]
  where
    bound = sizeBound - 1
    graph = either (error . show) id $ toFTA $ automatonNode description
    reference = either (error . show) id $ sizedReference graph

-- | A solver that fails when a property calls it.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> fail "unexpected solver call"

-- | The largest size that a property reads.
sizeBound :: Integer
sizeBound = 6

-- | A closed automaton with loops, overlapping alternatives, and equal children.
newtype SizedAutomaton = SizedAutomaton Automaton
    deriving (Show)

instance QC.Arbitrary SizedAutomaton where
    arbitrary = SizedAutomaton <$> QC.oneof [states 0 2, Loop <$> states 1 2] `QC.suchThat` closedAutomaton
      where
        states :: Int -> Int -> QC.Gen Automaton
        states loops budget = do
            count <- QC.chooseInt (1, 3)
            States <$> QC.vectorOf count (edge loops budget)
        edge loops budget = do
            (symbol, arity) <- QC.elements [entry | entry@(_, arity) <- symbolArities, budget > 0 || arity == 0]
            children <- QC.vectorOf arity (child loops (budget - 1))
            equal <- if arity == 2 then QC.frequency [(3, pure False), (1, pure True)] else pure False
            pure $ AutomatonEdge symbol children equal
        child loops budget =
            QC.frequency $
                [(2, Back <$> QC.chooseInt (0, loops - 1)) | loops > 0]
                    <> [(2, states loops budget), (1, Loop <$> states (loops + 1) budget)]

-- | The symbols of the automata and their arities.
symbolArities :: [(Text.Text, Int)]
symbolArities = [(Text.pack symbol, arity) | (symbol, arity) <- [("a", 0), ("b", 0), ("f", 1), ("g", 2), ("h", 2)]]

-- | Every term of the given size over the symbols of 'symbolArities'.
allTerms :: Integer -> [Term Symbol]
allTerms size =
    [ Term.Node (Symbol symbol) children
    | (symbol, arity) <- symbolArities
    , children <- spread arity (size - 1)
    ]
  where
    spread 0 0 = [[]]
    spread 0 _ = []
    spread arity remaining =
        [ first : rest
        | firstSize <- [1 .. remaining - toInteger (arity - 1)]
        , first <- allTerms firstSize
        , rest <- spread (arity - 1) (remaining - firstSize)
        ]

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> FTA.FTA String Symbol Constraint
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | The reference classes of an automaton from rows of named states.
fromReference :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> Sized Symbol
fromReference initial rows = either (error . show) id $ sizedReference $ automaton initial rows

-- | The size classes of an automaton from rows of named states.
fromRows :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> Sized Symbol
fromRows initial rows = either (error . show) id $ sized $ automaton initial rows

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
