{-# LANGUAGE PatternSynonyms #-}

module Data.CFTA.EGraphSpec (spec) where

import Control.Monad (forM_)
import Data.Functor.Identity (runIdentity)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
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
 )

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalitiesHold, equalityConstraint, noConstraint)
import Data.CFTA.EGraph
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Formula (Formula (..), Name (..), Relation (..))
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Index (Depth (..))
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Lattice (latticeImplies)
import Data.CFTA.Symbol (valueName)
import Data.CFTA.Term (Term, pattern Node)
import Data.Hashable (Hashable)
import qualified Data.Text as Text
import GHC.Generics (Generic)

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
build (Graph terms pairs) = foldl (\g (a, b) -> fromMaybe g (merge (ids !! a) (ids !! b) g)) g0 pairs
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
            , (2, traverse go ts >>= annotate sort . PNode f)
            ]
    annotate sort p = case sort of
        Nothing -> pure p
        Just s -> frequency [(2, pure p), (1, pure (PSorted (ground s) p)), (1, pure (PSorted (SVar (show s)) p))]
    ground (Node s ss) = SNode s (map ground ss)

termSize :: Term String -> Int
termSize (Node _ ts) = 1 + sum (map termSize ts)

{- | The least size of a term of the initial state of an automaton: the least
fixed point of the sizes that its transitions give. A cyclic automaton has
too many terms of each depth to list.
-}
leastSize :: (Ord state) => FTA.FTA state symbol constraint -> Maybe Int
leastSize automaton = Map.lookup (FTA.initialState automaton) (go Map.empty)
  where
    go sizes =
        let sizes' =
                Map.fromList
                    [ (q, minimum ks)
                    | q <- FTA.states automaton
                    , let ks =
                            [ 1 + sum cs | t <- FTA.transitionsFrom automaton q, Just cs <- [traverse (`Map.lookup` sizes) (FTA.transitionChildren t)]
                            ]
                    , not (null ks)
                    ]
         in if sizes' == sizes then sizes else go sizes'

-- An integer language with the length of a list: a literal, a variable, a length, a sum, and a quotient.
data Arith = Lit Integer | Var String | Len String | Plus | Quotient
    deriving (Eq, Ord, Show, Generic)

instance Hashable Arith

-- The values that an e-class can have: an interval, with no bound where Nothing.
data Interval = Interval (Maybe Integer) (Maybe Integer)
    deriving (Eq, Show)

{- An analysis of refinements: the interval of the value of each e-class. All
terms of an e-class have one value, so the join is the intersection: an
e-class knows what each of its e-nodes knows. A point is a constant, which
folds into its literal.
-}
refinements :: Analysis Arith Interval
refinements = Analysis make meet leaf
  where
    make (Lit n) [] = Interval (Just n) (Just n)
    make (Len _) [] = Interval (Just 0) Nothing
    make Plus [Interval a b, Interval c d] = Interval ((+) <$> a <*> c) ((+) <$> b <*> d)
    make Quotient [Interval (Just a) (Just b), Interval (Just c) (Just d)] | a == b, c == d, c /= 0 = Interval (Just (a `div` c)) (Just (a `div` c))
    make _ _ = Interval Nothing Nothing
    meet (Interval a b) (Interval c d) = Interval (bound max a c) (bound min b d)
    bound f x y = maybe y (\x' -> Just (maybe x' (f x') y)) x
    leaf (Interval (Just a) (Just b)) | a == b = Just (Lit a)
    leaf _ = Nothing

-- The refinement of an interval, a formula about the value.
refinement :: Interval -> Formula
refinement (Interval lo hi) =
    Formula.conjunction
        ([Atom Ge value (Formula.Lit a) | Just a <- [lo]] ++ [Atom Le value (Formula.Lit b) | Just b <- [hi]])
  where
    value = Formula.Var (Name (Text.pack valueName))

{- The condition that a variable is not zero: the refinement of its e-class
implies it, as the lattice of cfta decides without a solver.
-}
nonzero :: String -> Condition () Arith Interval
nonzero x = refines latticeImplies refinement x (Atom Ne (Formula.Var (Name (Text.pack valueName))) (Formula.Lit 0))

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
                        (Just (k, u), Right automaton) -> (k, termSize u, leastSize automaton) === (k, k, Just k)
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
    describe "an analysis of refinements" $ do
        let x = PVar "x"
            divide = either (error . show) id (rule (PNode Quotient [x, x]) (PNode (Lit 1) []))
            same lhs =
                let (c, g) = addTerm lhs (emptyEGraph :: EGraph () Arith)
                    (one, g') = addTerm (Node (Lit 1) []) g
                    (g'', _) = saturateWith (Saturation (Limits 10 1000 0) (Just refinements) Nothing) [(divide, nonzero "x")] g'
                 in equivalent g'' c one
            succLen = Node Plus [Node (Len "xs") [], Node (Lit 1) []]
        it "rewrites x / x to 1 when the refinement of x excludes 0" $
            same (Node Quotient [succLen, succLen]) `shouldBe` True
        it "does not rewrite x / x when the refinement of x allows 0" $
            same (Node Quotient [Node (Len "xs") [], Node (Len "xs") []]) `shouldBe` False
        it "folds a constant into its literal" $ do
            let (c, g) = addTerm (Node Plus [Node (Lit 2) [], Node (Lit 3) []]) (emptyEGraph :: EGraph () Arith)
                (five, g') = addTerm (Node (Lit 5) []) g
                (g'', _) = saturateWith (Saturation (Limits 10 1000 0) (Just refinements) Nothing) [] g'
            equivalent g'' c five `shouldBe` True
        it "reaches a goal that needs the analysis, and does not reach it without the analysis" $ do
            let (c, g) = addTerm (Node Quotient [succLen, succLen]) (emptyEGraph :: EGraph () Arith)
                (one, g') = addTerm (Node (Lit 1) []) g
                stop analysis = reportStop (snd (saturateWith (Saturation (Limits 10 1000 0) analysis (Just (c, one))) [(divide, nonzero "x")] g'))
            (stop (Just refinements), stop Nothing) `shouldBe` (Equal, Saturated)
    it "applies a rule only to the matches that its condition accepts" $ do
        let leaf s = Node s []
            (same, g1) = addTerm (Node "f" [leaf "a", leaf "a"]) (emptyEGraph :: EGraph () String)
            (other, g2) = addTerm (Node "f" [leaf "a", leaf "b"]) g1
            (c, g3) = addTerm (leaf "c") g2
            toC condition =
                let (g', _) = saturateWith defaultSaturation [(rewrite (PNode "f" [PVar "x", PVar "y"]) (PNode "c" []), condition)] g3
                 in (equivalent g' same c, equivalent g' other c)
        toC mempty `shouldBe` (True, True)
        toC (different "x" "y") `shouldBe` (False, True)
        toC (different "x" "y" <> different "y" "x") `shouldBe` (False, True)
        -- The rule has no variable z, so a condition on z is false.
        toC (different "x" "y" <> different "x" "z") `shouldBe` (False, False)
    it "keeps an e-class with an equality-constrained e-node to the terms that satisfy the constraint" $ do
        let leaf s = Node s []
            fOf x y = Node "f" [leaf x, leaf y]
            (a, g1) = addTerm (leaf "a") (emptyEGraph :: EGraph () String)
            (b, g2) = addTerm (leaf "b") g1
            -- One e-class holds a and b, so the plain e-node f(x, y) of it has four terms.
            ab = fromMaybe g2 (merge a b g2)
            sameChildren = equalityConstraint (mkEqConstraints [[path [0], path [1]]])
            (c, g3) = addConstrained sameChildren "f" [a, a] ab
            language g = case classAutomaton g c of
                Right automaton ->
                    Set.fromList
                        (runIdentity (FTA.termsUpToM (\_ t term -> pure (equalitiesHold (FTA.transitionConstraint t) term)) (Depth 2) automaton))
                Left _ -> Set.empty
            -- A rule matches the e-node as it matches its plain form.
            (g4, _) = saturate defaultLimits [rewrite (PNode "f" [PVar "x", PVar "y"]) (PNode "g" [PVar "y", PVar "x"])] g3
            -- The plain form is in the same e-class, and accepts all four pairs.
            (c', g5) = addTerm (fOf "a" "b") g3
            -- The terms by cost: the same terms, each once, also when the
            -- plain form and the e-node with the constraint share a row.
            byCost g = map snd (termsByCost (\_ ks -> 1 + sum ks :: Int) g c)
        language g3 `shouldBe` Set.fromList [fOf "a" "a", fOf "b" "b"]
        Set.size (language g4) `shouldBe` 6
        (find g5 c' == find g5 c, Set.size (language g5)) `shouldBe` (True, 4)
        forM_ [g3, g4, g5] $ \g -> (Set.fromList (byCost g), length (byCost g)) `shouldBe` (language g, Set.size (language g))
    describe "terms by cost" $ do
        let size _ children = 1 + sum children :: Int
        it "lists the n! * Catalan(n - 1) terms of an AC sum, each once, at the size of the sum" $
            forM_ [(3, 12), (4, 120), (5, 1680)] $ \(n, count) -> do
                let (c, g) = addTerm (sumOf n) emptyEGraph
                    (g', _) = saturate (Limits 100 100000 0) acRules g
                    found = termsByCost size g' c
                (length found, Set.size (Set.fromList (map snd found)), all ((== 2 * n - 1) . fst) found)
                    `shouldBe` (count, count, True)
        it "begins with a term of the cost of the extraction" $
            property $
                forAll genGraph $ \graph@(Graph terms _) -> forAll (elements terms) $ \t ->
                    let g = build graph
                        (c, _) = addTermWith (\(Sorted s f ts) -> (s, f, ts)) t g
                     in fmap fst (listToMaybe (termsByCost size g c)) === fmap fst (extract size g c)
        it "lists the infinite language of a cyclic e-class in the order of the cost" $ do
            -- x * 1 = x puts x * 1 in the e-class of x, so the e-class is a cycle.
            let leaf s = Node s []
                (c, g) = addTerm (leaf "x") (emptyEGraph :: EGraph () String)
                (_, g1) = addTerm (Node "*" [leaf "x", leaf "1"]) g
                (g', _) = saturate defaultLimits [rewrite (PNode "*" [PVar "y", PNode "1" []]) (PVar "y")] g1
                times t = Node "*" [t, leaf "1"]
            take 4 (termsByCost size g' c)
                `shouldBe` [(1, leaf "x"), (3, times (leaf "x")), (5, times (times (leaf "x"))), (7, times (times (times (leaf "x"))))]
    it "finds the e-class of a term without adding it, also through a merge" $ do
        let leaf s = Node s []
            (c, g1) = addTerm (Node "f" [leaf "a"]) (emptyEGraph :: EGraph () String)
            (b, g2) = addTerm (leaf "b") g1
            -- The e-graph has a, so adding it again gives its e-class.
            (a, _) = addTerm (leaf "a") g2
            merged = fromMaybe g2 (merge a b g2)
        (lookupTerm (Node "f" [leaf "a"]) g2, lookupTerm (Node "f" [leaf "b"]) g2) `shouldBe` (Just c, Nothing)
        lookupTerm (Node "f" [leaf "b"]) merged `shouldBe` Just (find merged c)
    it "does not stop while a rule with too many matches sits out" $
        -- With a match limit of 10, the rules of the AC sums sit out often.
        forM_ [4, 5, 6] $ \n -> do
            let (_, g) = addTerm (sumOf n) emptyEGraph
                (g', report) = saturate (Limits 100 100000 10) acRules g
            reportStop report `shouldBe` Saturated
            (eClassCount g', eNodeCount g') `shouldBe` (2 ^ n - 1, 3 ^ n - 2 ^ (n + 1) + n + 1)
    it "holds the n! * Catalan(n - 1) terms of an AC sum of n variables, in 3^n - 2^(n+1) + n + 1 e-nodes" $
        forM_ [(3, 12), (4, 120), (5, 1680)] $ \(n, count) -> do
            let (c, g) = addTerm (sumOf n) emptyEGraph
                (g', report) = saturate (Limits 100 100000 0) acRules g
            reportStop report `shouldBe` Saturated
            (eClassCount g', eNodeCount g') `shouldBe` (2 ^ n - 1, 3 ^ n - 2 ^ (n + 1) + n + 1)
            fmap (length . FTA.terms) (classAutomaton g' c) `shouldBe` Right count
