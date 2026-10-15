{-# LANGUAGE OverloadedStrings #-}

{- | Check each component of the interned automata against "Data.CFTA.Simple".

The automata are random explicit automata over at most three states, with
cycles and with equality constraints, some of which name a child that does
not exist. Each property compares one component with the definition in
"Data.CFTA.Simple": membership, enumeration, the constructions, and the
reductions. Terms are compared up to depth two, or three when the automaton
has few trees.
-}
module Data.CFTA.SimpleSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_)
import Data.Functor.Identity (Identity (..))
import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)
import Test.QuickCheck (Gen, chooseInt, classify, elements, forAll, property, vectorOf, within)

import Data.CFTA (FTA, Transition (Transition), mapConstraints, mkFTA)
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint,
    conjoinConstraints,
    constraintPaths,
    equalitiesHold,
    equalityConstraint,
    noConstraint,
 )
import Data.CFTA.Enumeration (
    PartialSymbol (ConcreteSymbol),
    expandPartialTermFrag,
    noExpansionPreference,
    runs,
    runsBy,
    runsInterned,
    terms,
    termsPruneWith,
    truncatedTerms,
 )
import Data.CFTA.Equality (
    accepts,
    dropConstraints,
    fixUnbounded,
    mkEqConstraints,
    reducePartially,
    termsMatching,
    withoutRedundantEdges,
 )
import Data.CFTA.Index (Depth)
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (ChildIndex (..), path, unPath)
import qualified Data.CFTA.Simple as Simple
import Data.CFTA.Template (
    Template (..),
    exclude,
    excludeAnywhere,
    excludeAnywhereFTA,
    excludeFTA,
    matchesNone,
    matchesNowhere,
    matchesTemplate,
    restrictFTA,
 )
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "the interned automata against Data.CFTA.Simple" $ do
    it "accept the terms that the simple definition accepts, also after toFTA" $
        property $
            forAll automaton $ \explicit -> do
                let node = Interned.fromFTA explicit
                [(term, accepts node term) | term <- candidates explicit]
                    `shouldBe` [(term, simpleAccepts explicit term) | term <- candidates explicit]
                case Interned.toFTA node of
                    Left err -> expectationFailure $ show err
                    Right viewed ->
                        [(term, Simple.accepts viewed term) | term <- candidates explicit]
                            `shouldBe` [(term, Simple.accepts explicit term) | term <- candidates explicit]

    it "accept at the explicit view the terms that the simple definition accepts" $
        property $
            forAll automaton $ \explicit ->
                [(term, FTA.accepts explicit term) | term <- candidates explicit]
                    `shouldBe` [(term, simpleAccepts explicit term) | term <- candidates explicit]

    it "list at the explicit view the trees of the underlying graph up to each depth" $
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (FTA.terms (FTA.boundDepth depth explicit))) `shouldBe` (depth, underlying depth explicit)

    it "check at the explicit view the terms that the simple definition accepts and lists" $
        property $
            forAll automaton $ \explicit -> within 10000000 $ do
                let check _ transition term = Identity $ equalitiesHold (FTA.transitionConstraint transition) term
                [(term, runIdentity (FTA.acceptsM check explicit term)) | term <- candidates explicit]
                    `shouldBe` [(term, simpleAccepts explicit term) | term <- candidates explicit]
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (runIdentity (FTA.termsUpToM check depth explicit))) `shouldBe` (depth, simpleTerms depth explicit)

    it "restrict the explicit view to a template as filtering its trees does" $
        property $
            forAll ((,) <$> automaton <*> template) $ \(explicit, shape) -> within 10000000 $
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (FTA.terms (FTA.boundDepth depth (restrictFTA shape explicit))))
                        `shouldBe` (depth, filter (matchesTemplate shape) (underlying depth explicit))

    it "exclude templates from the explicit view as filtering its trees does" $
        property $
            forAll ((,) <$> automaton <*> templates) $ \(explicit, shapes) -> within 10000000 $
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (FTA.terms (FTA.boundDepth depth (excludeFTA shapes explicit))))
                        `shouldBe` (depth, filter (matchesNone shapes) (underlying depth explicit))

    it "exclude templates from the explicit view and the interned view with no new ambiguity" $
        -- For an ambiguous input, the number of runs of a term can change:
        -- interning merges copies that become equal, and an equality
        -- constraint ties the runs of two children that the split makes
        -- different. A term with one run in the input has one run in the
        -- result.
        property $
            forAll ((,) <$> automaton <*> templates) $ \(explicit, shapes) ->
                let node = Interned.fromFTA explicit
                 in within 10000000 $
                        classify (all (== 1) (runCounts (deepest explicit) node)) "unambiguous input" $
                            forM_ [0 .. deepest explicit] $ \depth -> do
                                let kept = Map.filterWithKey (\term _ -> matchesNone shapes term) (runCounts depth node)
                                    check result = (depth, termsAndAmbiguity (runCounts depth result) kept) `shouldBe` (depth, (Map.keys kept, []))
                                check (exclude shapes node)
                                check (Interned.fromFTA (excludeFTA shapes explicit))

    it "exclude templates from the explicit view with one run for each run of the input that it keeps" $
        property $
            forAll ((,) <$> automaton <*> templates) $ \(explicit, shapes) -> within 10000000 $ do
                let excluded = excludeFTA shapes explicit
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, [explicitRuns excluded (FTA.initialState excluded) term | term <- underlying depth explicit])
                        `shouldBe` (depth, [if matchesNone shapes term then explicitRuns explicit 0 term else 0 | term <- underlying depth explicit])

    it "exclude templates anywhere from the explicit view as filtering its trees does" $
        property $
            forAll ((,) <$> automaton <*> templates) $ \(explicit, shapes) -> within 10000000 $
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (FTA.terms (FTA.boundDepth depth (excludeAnywhereFTA shapes explicit))))
                        `shouldBe` (depth, filter (matchesNowhere shapes) (underlying depth explicit))

    it "exclude templates anywhere from the explicit view with one run for each run of the input that it keeps" $
        property $
            forAll ((,) <$> automaton <*> templates) $ \(explicit, shapes) -> within 10000000 $ do
                let excluded = excludeAnywhereFTA shapes explicit
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, [explicitRuns excluded (FTA.initialState excluded) term | term <- underlying depth explicit])
                        `shouldBe` (depth, [if matchesNowhere shapes term then explicitRuns explicit 0 term else 0 | term <- underlying depth explicit])

    it "exclude templates anywhere from the explicit view and the interned view with no new ambiguity" $
        -- As for excludeFTA, a term with one run in the input has one run in
        -- the result. The automata have cycles, so the results of both
        -- constructions are recursive. A state of the result pairs a state
        -- with an obligation, so a component of the result can have about ten
        -- states.
        property $
            forAll ((,) <$> automaton <*> templates) $ \(explicit, shapes) ->
                let node = Interned.fromFTA explicit
                 in within 10000000 $
                        classify (all (== 1) (runCounts (deepest explicit) node)) "unambiguous input" $
                            forM_ [0 .. deepest explicit] $ \depth -> do
                                let kept = Map.filterWithKey (\term _ -> matchesNowhere shapes term) (runCounts depth node)
                                    check result = (depth, termsAndAmbiguity (runCounts depth result) kept) `shouldBe` (depth, (Map.keys kept, []))
                                check (excludeAnywhere shapes node)
                                check (Interned.fromFTA (excludeAnywhereFTA shapes explicit))

    it "exclude templates anywhere from a chain whose function children no template fits" $ do
        -- A cell of Specftacular's lists-5-1 at size 5, in its curried
        -- encoding: an application has the children [type, (->), function,
        -- argument], and a symbol has its type as its one child. Every
        -- template has the root app, and its function part has a root that
        -- the function children (f0) do not have. Before #34, the split
        -- over every subset of the templates at the function child did not
        -- end within a minute; with the ground parts grouped, it made 3,521
        -- copies and 190 states; now each edge has one copy. No template
        -- matches, so the result keeps the one term.
        let a = TemplateNode "Spectacular.Types.A" []
            int = TemplateNode "GHC.Internal.Types.Int" []
            list t = TemplateNode "[]" [t]
            t ~> u = TemplateNode "->" [TemplateNode "(->)" [], t, u]
            infixr 5 ~>
            sym name t = TemplateNode name [t]
            var t = AnyPrefix [t]
            app f v = TemplateNode "app" [Hole, Hole, f, v]
            append = sym "++" (list a ~> list a ~> list a)
            nil = sym "[]" (list a)
            len = sym "length" (list a ~> int)
            rev = sym "reverse" (list a ~> list a)
            mapping = sym "map" ((a ~> a) ~> list a ~> list a)
            shapes =
                [ app (app append nil) (var (list a))
                , app (app append (var (list a))) nil
                , app len (app (app append (app rev (var (list a)))) (var (list a)))
                , app len (app (app append (var (list a))) (app rev (var (list a))))
                , app len (app (app mapping (var (a ~> a))) (var (list a)))
                , app len (app rev (var (list a)))
                , app len nil
                , app (app mapping (var (a ~> a))) (app rev (var (list a)))
                , app (app mapping (var (a ~> a))) nil
                , app rev (app rev (var (list a)))
                , app rev nil
                ]
            leaf symbol = [Transition symbol [] noConstraint]
            edge symbol children = [Transition symbol children noConstraint]
            rows =
                Map.fromList
                    [ (1, leaf "(->)")
                    , (2, leaf "Spectacular.Types.A")
                    , (3, edge "->" [1, 2, 2])
                    , (29, edge "x0_<A>" [2])
                    , (52, edge "f0_<A -> A>" [3])
                    , (53, edge "app" [2, 1, 52, 29])
                    , (80, edge "app" [2, 1, 52, 53])
                    , (115, edge "app" [2, 1, 52, 80])
                    , (143, edge "app" [2, 1, 52, 115])
                    , (144, edge "filter" [2, 143])
                    ]
            space = Interned.fromRows (144 :: Int) rows
        result <- timeout 10000000 $ evaluate $ runCounts 12 (excludeAnywhere shapes space)
        result `shouldBe` Just (runCounts 12 space)
        Map.elems (runCounts 12 space) `shouldBe` [1]

    it "enumerate the terms up to each depth that the simple definition lists" $
        property $
            forAll automaton $ \explicit -> do
                let node = Interned.fromFTA explicit
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let expected = simpleTerms depth explicit
                        bounded = Interned.boundDepth depth node
                    (depth, sort (terms bounded)) `shouldBe` (depth, expected)
                    (depth, Set.fromList [term | partial <- truncatedTerms bounded, Just term <- [traverse concrete partial]])
                        `shouldBe` (depth, Set.fromList expected)
                    (depth, Set.fromList [term | (term, []) <- runs "Mu" bounded]) `shouldBe` (depth, Set.fromList expected)

    it "list with weights on the edges the runs that runs lists, in another order" $
        -- The weights put more children and later symbols first, against the
        -- canonical order.
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let bounded = Interned.boundDepth depth (Interned.fromFTA explicit)
                        weight edge = fromIntegral (100 * length (Interned.edgeChildren edge) + sum (map fromEnum (Interned.edgeSymbol edge)))
                    (depth, sort (map fst (runsBy weight "Mu" bounded))) `shouldBe` (depth, sort (map fst (runs "Mu" bounded)))

    it "list in the interning order the runs that runs lists, in another order" $
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let bounded = Interned.boundDepth depth (Interned.fromFTA explicit)
                    (depth, sort (map fst (runsInterned "Mu" bounded))) `shouldBe` (depth, sort (map fst (runs "Mu" bounded)))

    it "prune with an oracle as filtering the terms by the oracle does, in either expansion order" $
        -- The oracle rejects every fragment that holds a "b". A fragment only
        -- grows, so the rejection is monotone and the order does not matter.
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let bounded = Interned.boundDepth depth (Interned.fromFTA explicit)
                        oracle _ _ (Left fragment) = do
                            partial <- expandPartialTermFrag fragment
                            return (holdsB partial, ())
                        oracle _ _ (Right _) = return (False, ())
                        holdsB (Term.Node (ConcreteSymbol symbol) children) = symbol == "b" || any holdsB children
                        holdsB (Term.Node _ children) = any holdsB children
                        preferLast _ holes = case reverse holes of
                            uv : _ -> Just uv
                            [] -> Nothing
                        expected = Set.fromList $ filter (notElem "b" . Term.flatten) (simpleTerms depth explicit)
                    (depth, Set.fromList (termsPruneWith "Mu" () noExpansionPreference oracle bounded)) `shouldBe` (depth, expected)
                    (depth, Set.fromList (termsPruneWith "Mu" () preferLast oracle bounded)) `shouldBe` (depth, expected)

    it "intersect as the simple product does, which keeps the terms of both" $
        property $
            forAll ((,) <$> automaton <*> automaton) $ \(left, right) ->
                forM_ [0 .. min (deepest left) (deepest right)] $ \depth -> do
                    let expected = simpleTerms depth (Simple.intersect left right)
                    (depth, expected) `shouldBe` (depth, filter (simpleAccepts right) (simpleTerms depth left))
                    (depth, sort (terms (Interned.boundDepth depth (Interned.intersect (Interned.fromFTA left) (Interned.fromFTA right)))))
                        `shouldBe` (depth, expected)
                    case FTA.intersectWith sameSymbol conjoinConstraints left right of
                        Left err -> expectationFailure $ show err
                        Right explicitProduct -> (depth, simpleTerms depth explicitProduct) `shouldBe` (depth, expected)

    it "unite as the simple union does, which keeps the terms of either" $
        property $
            forAll ((,) <$> automaton <*> automaton) $ \(left, right) ->
                forM_ [0 .. min (deepest left) (deepest right)] $ \depth -> do
                    let expected = simpleTerms depth (Simple.union left right)
                    (depth, expected) `shouldBe` (depth, Set.toList $ Set.fromList $ simpleTerms depth left <> simpleTerms depth right)
                    (depth, sort (terms (Interned.boundDepth depth (Interned.union [Interned.fromFTA left, Interned.fromFTA right]))))
                        `shouldBe` (depth, expected)

    it "bound the depth as the simple bound does, which keeps the shallow terms" $
        property $
            forAll automaton $ \explicit ->
                forM_ [-1 .. deepest explicit] $ \depth -> do
                    let bounded = Simple.boundDepth depth explicit
                        shallow = filter ((<= depth) . treeDepth) (candidates explicit)
                    (depth, [(term, simpleAccepts bounded term) | term <- candidates explicit])
                        `shouldBe` (depth, [(term, term `elem` shallow && simpleAccepts explicit term) | term <- candidates explicit])
                    (depth, [(term, accepts (Interned.boundDepth depth (Interned.fromFTA explicit)) term) | term <- candidates explicit])
                        `shouldBe` (depth, [(term, simpleAccepts bounded term) | term <- candidates explicit])

    it "restrict to a template as filtering the terms by the template does" $
        property $
            forAll ((,) <$> automaton <*> template) $ \(explicit, shape) ->
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (terms (Interned.boundDepth depth (termsMatching shape (Interned.fromFTA explicit)))))
                        `shouldBe` (depth, filter (matchesTemplate shape) (simpleTerms depth explicit))

    it "keep the language through each reduction" $
        -- Two states at most: the interned form nests a binder for each state
        -- of a cycle on every path, so three mutually recursive states can make
        -- withoutRedundantEdges, which intersects nodes, take seconds. The
        -- limit reports such a case rather than hanging.
        property $
            forAll (automatonOf 2) $ \explicit -> within 20000000 $ do
                let node = Interned.fromFTA explicit
                forM_ reductions $ \(name, reduce) -> do
                    let reduced = reduce node
                    (name, [(term, accepts reduced term) | term <- candidates explicit])
                        `shouldBe` (name, [(term, simpleAccepts explicit term) | term <- candidates explicit])
                    forM_ [0 .. deepest explicit] $ \depth ->
                        (name, depth, sort (terms (Interned.boundDepth depth reduced))) `shouldBe` (name, depth, simpleTerms depth explicit)

    it "drop the constraints to the underlying graph of the transitions that can accept" $
        -- An interned edge whose class names a child it does not have accepts
        -- nothing, and interning removes it, so dropping constraints cannot
        -- bring it back.
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (terms (Interned.boundDepth depth (dropConstraints (Interned.fromFTA explicit)))))
                        `shouldBe` (depth, underlying depth (withoutMissingChildren explicit))

    it "unfold recursion to a part of the language that grows with the rounds" $
        -- Two states at most, for the nesting of binders, as for the reductions.
        property $
            forAll (automatonOf 2) $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let listed rounds = Set.fromList $ terms $ Interned.boundDepth depth $ Interned.unfoldBounded rounds $ Interned.fromFTA explicit
                        growing = [listed rounds | rounds <- [0 .. 3]] <> [Set.fromList (simpleTerms depth explicit)]
                    (depth, and (zipWith Set.isSubsetOf growing (drop 1 growing))) `shouldBe` (depth, True)
  where
    reductions =
        [ ("reducePartially" :: String, reducePartially)
        , ("withoutRedundantEdges", withoutRedundantEdges)
        , ("both to a fixpoint", fixUnbounded (withoutRedundantEdges . reducePartially))
        ]
    sameSymbol left right = if left == right then Just left else Nothing
    treeDepth (Term.Node _ []) = 0 :: Depth
    treeDepth (Term.Node _ children) = 1 + maximum (map treeDepth children)
    concrete (ConcreteSymbol symbol) = Just symbol
    concrete _ = Nothing

-- | A random explicit automaton: at most three states, one arity per symbol, and equality constraints.
automaton :: Gen (FTA Int String Constraint)
automaton = automatonOf 3

-- | A random explicit automaton over at most the given number of states.
automatonOf :: Int -> Gen (FTA Int String Constraint)
automatonOf states = do
    count <- chooseInt (1, states)
    rows <- forM [0 .. count - 1] $ \state -> do
        width <- chooseInt (1, 3)
        (,) state <$> vectorOf width (transition count)
    pure $ either (error . show) id $ mkFTA 0 rows
  where
    transition count = do
        (symbol, arity) <- elements [("a", 0), ("b", 0), ("f", 1), ("g", 2)]
        children <- vectorOf arity (chooseInt (0, count - 1))
        classes <- elements $ case arity of
            0 -> [[]]
            1 -> [[], [], [[path [0, 0], path [0, 1]]]]
            _ ->
                [ []
                , []
                , [[path [0], path [1]]]
                , [[path [0, 0], path [1]]]
                , [[path [0, 1], path [1, 0]]]
                , [[path [0], path [2]]]
                ]
        pure $ Transition symbol children $ if null classes then noConstraint else equalityConstraint $ mkEqConstraints classes

-- | A random template over the symbols of 'automaton', two levels deep at most.
template :: Gen (Template String)
template = go (2 :: Int)
  where
    go 0 = pure Hole
    go depth = do
        children <- chooseInt (0, 2) >>= \count -> vectorOf count (go (depth - 1))
        symbol <- elements ["a", "b", "f", "g"]
        elements [Hole, AnyNode children, TemplateNode symbol children, AnyPrefix children, TemplatePrefix symbol children]

-- | At most three random templates.
templates :: Gen [Template String]
templates = chooseInt (0, 3) >>= \count -> vectorOf count template

-- | The automaton without the transitions whose constraints name a child that they do not have.
withoutMissingChildren :: FTA Int String Constraint -> FTA Int String Constraint
withoutMissingChildren explicit =
    either (error . show) id $
        mkFTA
            (FTA.initialState explicit)
            [(state, filter fits (FTA.transitionsFrom explicit state)) | state <- FTA.states explicit]
  where
    fits (Transition _ children constraint) =
        and
            [0 <= index && index < length children | ChildIndex index : _ <- map unPath (Set.toList $ constraintPaths constraint)]

-- | The deepest depth to compare: three when the underlying graph has few trees of depth two.
deepest :: FTA Int String Constraint -> Depth
deepest explicit
    | length (underlying 2 explicit) <= 40 = 3
    | otherwise = 2

-- | The number of runs of an explicit automaton from a state on a term, whose constraints hold on the term.
explicitRuns :: (Ord state) => FTA state String Constraint -> state -> Term String -> Integer
explicitRuns explicit state term@(Term.Node symbol children) =
    sum
        [ product (zipWith (explicitRuns explicit) (FTA.transitionChildren transition) children)
        | transition <- FTA.transitionsFrom explicit state
        , FTA.transitionSymbol transition == symbol
        , length (FTA.transitionChildren transition) == length children
        , equalitiesHold (FTA.transitionConstraint transition) term
        ]

-- | The number of runs of each term of a node up to a depth.
runCounts :: Depth -> Interned.Node String -> Map (Term String) Int
runCounts depth = Map.fromListWith (+) . map (\(term, _) -> (term, 1)) . runs "Mu" . Interned.boundDepth depth

{- | The terms of a result, and the terms with one run in the input that have
more runs in the result.
-}
termsAndAmbiguity :: (Ord term) => Map term Int -> Map term Int -> ([term], [term])
termsAndAmbiguity result input = (Map.keys result, [term | (term, 1) <- Map.toList input, Map.findWithDefault 0 term result > 1])

-- | The trees of the underlying graph up to a depth, without constraints.
underlying :: Depth -> FTA Int String Constraint -> [Term String]
underlying depth = fromMaybe [] . Simple.termsUpTo depth . mapConstraints (const noConstraint)

-- | Terms to test membership of: the trees of the underlying graph, and trees with a foreign symbol.
candidates :: FTA Int String Constraint -> [Term String]
candidates explicit = underlying (deepest explicit) explicit <> [Term.Node "c" [], Term.Node "f" [Term.Node "c" []]]

simpleAccepts :: (Ord state) => FTA state String Constraint -> Term String -> Bool
simpleAccepts explicit = fromMaybe (error "an equality constraint needed a solver") . Simple.accepts explicit

simpleTerms :: (Ord state) => Depth -> FTA state String Constraint -> [Term String]
simpleTerms depth = fromMaybe (error "an equality constraint needed a solver") . Simple.termsUpTo depth
