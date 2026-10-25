{-# LANGUAGE PatternSynonyms #-}

module Data.CFTA.EGraphSpec (spec) where

import Control.Monad (forM_)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)
import Test.QuickCheck (
    Gen,
    choose,
    counterexample,
    elements,
    forAll,
    frequency,
    oneof,
    property,
    vectorOf,
    (===),
    (==>),
 )

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalitiesHold, equalityConstraint, noConstraint)
import Data.CFTA.EGraph
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Index (Depth (..))
import Data.CFTA.Path (path)
import Data.CFTA.Term (Term, pattern Node)

-- A term with a sort at each node, for 'addTermWith'.
data Sorted = Sorted (Maybe (Term String)) String [Sorted]
    deriving (Show)

-- Some terms, and the pairs of them to merge.
data Graph = Graph [Sorted] [(Int, Int)]
    deriving (Show)

genSorted :: Int -> Gen Sorted
genSorted depth = do
    sort <- elements [Nothing, Just (Node "S" []), Just (Node "T" []), Just (Node "List" [Node "S" []])]
    let leaf = (\a -> Sorted sort a []) <$> elements ["a", "b"]
    if depth <= 0
        then leaf
        else
            oneof
                [ leaf
                , (\t -> Sorted sort "g" [t]) <$> genSorted (depth - 1)
                , (\t u -> Sorted sort "f" [t, u]) <$> genSorted (depth - 1) <*> genSorted (depth - 1)
                , (\t -> Sorted sort "f" [t, t]) <$> genSorted (depth - 1)
                ]

genGraph :: Gen Graph
genGraph = do
    terms <- choose (1, 5) >>= \n -> vectorOf n (genSorted 3)
    pairs <- choose (0, 3) >>= \n -> vectorOf n ((,) <$> choose (0, length terms - 1) <*> choose (0, length terms - 1))
    pure (Graph terms pairs)

-- The e-graph of the terms, after the merges of terms with one sort.
build :: Graph -> EGraph String String
build (Graph terms pairs) = foldl (\g (a, b) -> maybe g id (merge (ids !! a) (ids !! b) g)) g0 pairs
  where
    (ids, g0) = foldl (\(acc, g) t -> let (c, g') = addTermWith view t g in (acc ++ [c], g')) ([], emptyEGraph) terms
    view (Sorted sort f ts) = (sort, f, ts)

genPattern :: Int -> Gen (Pattern String String)
genPattern depth = do
    let leaf = oneof [PVar <$> elements ["x", "y"], (`PNode` []) <$> elements ["a", "b"]]
    p <-
        if depth <= 0
            then leaf
            else
                oneof
                    [ leaf
                    , (\q -> PNode "g" [q]) <$> genPattern (depth - 1)
                    , (\q r -> PNode "f" [q, r]) <$> genPattern (depth - 1) <*> genPattern (depth - 1)
                    ]
    frequency [(2, pure p), (1, (`PSorted` p) <$> genSort)]
  where
    genSort = elements [SVar "s", SVar "u", SNode "S" [], SNode "T" [], SNode "List" [SVar "s"], SNode "List" [SNode "S" []]]

{- A pattern from a term of the e-graph: some subterms become variables, and
some nodes get their sorts. A variable is named after its e-class, and a
sort variable after its sort, so that equal e-classes and equal sorts give a
variable that occurs twice.
-}
genAbstraction :: Graph -> Gen (Pattern String String)
genAbstraction graph@(Graph terms _) = elements terms >>= go
  where
    g = build graph
    go t@(Sorted sort f ts) = do
        let (c, _) = addTermWith (\(Sorted s h us) -> (s, h, us)) t g
        frequency
            [ (1, pure (PVar (show (find g c))))
            , (2, PNode f <$> traverse go ts >>= annotate sort)
            ]
    annotate sort p = case sort of
        Nothing -> pure p
        Just s -> frequency [(2, pure p), (1, pure (PSorted (ground s) p)), (1, pure (PSorted (SVar (show s)) p))]
    ground (Node s ss) = SNode s (map ground ss)

termSize :: Term String -> Int
termSize (Node _ ts) = 1 + sum (map termSize ts)

termDepth :: Term String -> Int
termDepth (Node _ []) = 0
termDepth (Node _ ts) = 1 + maximum (map termDepth ts)

-- The sum x1 + ... + xn, associated to the left.
sumOf :: Int -> Term String
sumOf n = foldl1 (\a b -> Node "+" [a, b]) [Node ('x' : show i) [] | i <- [1 .. n]]

acRules :: [Rule String String]
acRules = either (error . show) id (rule (x .+ y) (y .+ x)) : equation ((x .+ y) .+ z) (x .+ (y .+ z))
  where
    a .+ b = PNode "+" [a, b]
    x = PVar "x"
    y = PVar "y"
    z = PVar "z"

spec :: Spec
spec = describe "Data.CFTA.EGraph" $ do
    it "matches a pattern as the terms of the product of the e-graph and pattern automata" $
        property $
            forAll genGraph $ \graph -> forAll (oneof [genPattern 2, genAbstraction graph]) $ \p ->
                let g = build graph in Set.fromList (ematch g p) === Set.fromList (ematchByIntersection g p)
    it "extracts a term of the least size of the language of an e-class" $
        property $
            forAll genGraph $ \graph@(Graph terms _) -> forAll (elements terms) $ \t ->
                let g = build graph
                    (c, _) = addTermWith (\(Sorted s f ts) -> (s, f, ts)) t g
                 in case (extract (\_ ks -> 1 + sum ks) g c, classAutomaton g c) of
                        (Just (k, u), Right automaton) ->
                            -- The terms of depth at most k, which hold every term of size k.
                            let shallow = take 20001 (takeWhile ((<= k) . termDepth) (FTA.terms automaton))
                             in length shallow <= 20000 ==> (k, termSize u, minimum (map termSize shallow)) === (k, k, k)
                        (e, a) -> counterexample (show (fmap fst e, either show (const "an automaton") a)) False
    it "selects the terms of an e-class with an ECTA" $ do
        -- Under distributivity and commutativity, the e-class of a * (b + c)
        -- holds a*b + a*c. The ECTA accepts the sums whose two summands have
        -- equal left factors: the paths [0, 0] and [1, 0] hold equal terms.
        let x = PVar "x"
            y = PVar "y"
            z = PVar "z"
            a .* b = PNode "*" [a, b]
            a .+ b = PNode "+" [a, b]
            rules = equation (x .* (y .+ z)) ((x .* y) .+ (x .* z)) ++ equation (x .+ y) (y .+ x) ++ equation (x .* y) (y .* x)
            leaf s = Node s []
            (c, g) = addTerm (Node "*" [leaf "a", Node "+" [leaf "b", leaf "c"]]) (emptyEGraph :: EGraph String String)
            (g', _) = saturate (Limits 10 10000 0) rules g
            anyTerm = [FTA.Transition f cs noConstraint | (f, cs) <- [("a", []), ("b", []), ("c", []), ("+", [2, 2]), ("*", [2, 2])]]
            sharedFactor =
                FTA.mkFTA
                    (0 :: Int)
                    [ (0, [FTA.Transition "+" [1, 1] (equalityConstraint (mkEqConstraints [[path [0, 0], path [1, 0]]]))])
                    , (1, [FTA.Transition "*" [2, 2] noConstraint])
                    , (2, anyTerm)
                    ]
        case (classAutomaton g' c, sharedFactor) of
            (Right language, Right selection) -> case FTA.intersectWith (\f h -> if f == h then Just f else Nothing) (\_ k -> k) language selection of
                Right both -> do
                    found <- FTA.termsUpToM (\_ t u -> pure (equalitiesHold (FTA.transitionConstraint t) u)) (Depth 3) both
                    Set.fromList found
                        `shouldBe` Set.fromList
                            [ Node "+" [Node "*" [leaf "a", leaf "b"], Node "*" [leaf "a", leaf "c"]]
                            , Node "+" [Node "*" [leaf "a", leaf "c"], Node "*" [leaf "a", leaf "b"]]
                            ]
                Left err -> expectationFailure (show err)
            _ -> expectationFailure "no automaton"
    it "holds the n! * Catalan(n - 1) terms of an AC sum of n variables, in 3^n - 2^(n+1) + n + 1 e-nodes" $
        forM_ [(3, 12), (4, 120), (5, 1680)] $ \(n, count) -> do
            let (c, g) = addTerm (sumOf n) emptyEGraph
                (g', report) = saturate (Limits 100 100000 0) acRules g
            reportStop report `shouldBe` Saturated
            (eClassCount g', eNodeCount g') `shouldBe` (2 ^ n - 1, 3 ^ n - 2 ^ (n + 1) + n + 1)
            fmap (length . FTA.terms) (classAutomaton g' c) `shouldBe` Right count
