module Data.CFTA.SizedSpec (spec) where

import Control.Monad (forM_, void)
import Data.Containers.ListUtils (nubOrd)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Data.Word (Word64)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck (Property, counterexample, (.&&.), (===))
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (..), equalityConstraint, noConstraint, semanticConstraint)
import Data.CFTA.Equality (numNestedMu)
import qualified Data.CFTA.Equality as ECTA
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Reference (Automaton (..), AutomatonEdge (..), automatonNode, closedAutomaton)
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size (..), Weight (..))
import Data.CFTA.Interned (toFTA)
import qualified Data.CFTA.Language as Language
import qualified Data.CFTA.Language.Source as Source
import Data.CFTA.Lowering (Expansion (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Refinement (Entailment (Entailment))
import Data.CFTA.Sized
import Data.CFTA.Sized.Checkpoint (Checkpoint (..), CheckpointError (..), SamplingCheckpoint (..))
import qualified Data.CFTA.Sized.Checkpoint as Checkpoint
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Template (Exclusion (..), Template (..), matchesNone, matchesNowhere)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Sized" $ do
    it "counts and ranks the inverse image of a spec under a template lowering" $ do
        -- double(x) lowers to add(x, x). The spec keeps the sums with an even value.
        let lowering = either (error . show) id $ Lowering.mkLowering [(sym "double", 1, Apply (sym "add") [Child 0, Child 0])]
            later = automaton "e" [("e", [leaf "zero", leaf "one", node "add" ["e", "e"], node "double" ["e"]])]
            evenValue =
                automaton
                    "even"
                    [ ("even", [leaf "zero", node "add" ["even", "even"], node "add" ["odd", "odd"]])
                    , ("odd", [leaf "one", node "add" ["even", "odd"], node "add" ["odd", "even"]])
                    ]
            lifted = either (error . show) id $ Lowering.lift lowering evenValue
            within = either (error . show) id $ sized $ FTA.dropConstraints $ FTA.intersect later lifted
            whole = either (error . show) id $ sized later
            keeps candidate = maybe False (FTA.accepts evenValue) (Lowering.lower lowering candidate)
        forM_ [1 .. 7] $ \size -> do
            sort (termsOfSize within size) `shouldBe` sort (filter keeps (termsOfSize whole size))
            let Cardinality count = countOfSize within size
            forM_ [0 .. count - 1] $ \rank ->
                (rankOfSize within =<< unrankOfSize within size (ClassRank rank)) `shouldBe` Just (size, ClassRank rank)
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
    it "keeps the row order of two transitions that differ only in constraints" $ do
        -- The sort key of a transition has no constraints, and the sort is
        -- stable. A change to the sort key changes these classes.
        let equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]
            pairs constraint = FTA.Transition (sym "g") ["t", "t"] constraint
            pairOf left right = term "g" [term left [], term right []]
            leaves = ("t", [leaf "a", leaf "b"])
            -- The two transitions differ in their constraints.
            onRoot first second = fromRows "s" [("s", [pairs first, pairs second]), leaves]
            -- The two transitions differ in the constraints of their child states.
            below first second =
                fromRows "s" [("s", [node "f" [first], node "f" [second]]), ("p", [pairs equal]), ("q", [pairs noConstraint]), leaves]
        termsOfSize (onRoot equal noConstraint) 3 `shouldBe` [pairOf "a" "a", pairOf "b" "b", pairOf "a" "b", pairOf "b" "a"]
        termsOfSize (onRoot noConstraint equal) 3 `shouldBe` [pairOf "a" "a", pairOf "a" "b", pairOf "b" "a", pairOf "b" "b"]
        termsOfSize (below "p" "q") 4
            `shouldBe` map (term "f" . pure) [pairOf "a" "a", pairOf "b" "b", pairOf "a" "b", pairOf "b" "a"]
        termsOfSize (below "q" "p") 4
            `shouldBe` map (term "f" . pure) [pairOf "a" "a", pairOf "a" "b", pairOf "b" "a", pairOf "b" "b"]
    it "rejects a guard beyond equality constraints" $ do
        let different = semanticConstraint $ Not $ Same (ECTA.path [0]) (ECTA.path [1])
            rows = [("s", [FTA.Transition (sym "g") ["q", "q"] different]), ("q", [leaf "a", leaf "b"])]
        either Just (const Nothing) (sized $ automaton "s" rows) `shouldBe` Just ResidualGuard
    modifyMaxSuccess (const 300) $ do
        it "lists each accepted term of each size once, and ranks it" $ QC.property exactClasses
        it "agrees with the cyclic import wherever the import accepts the automaton" $ QC.property importAgreement
        it "gives the sequence of the reference, also where it uses the count table" $ QC.property referenceAgreement
        it "gives the classes of sized for each state, from one table" $ QC.property stateAgreement
        it "decides the classes up to a bound as the reference builds them" $ QC.property boundedAgreement
    describe "Data.CFTA.Sized.Checkpoint" $ do
        it "resumes at every cut as the listing without a cut" $
            forM_ listings $ \graph -> do
                let entries = listing graph
                    classes = either (error . show) id $ sized graph
                map fst entries `shouldBe` concatMap (termsOfSize classes) [1 .. listingBound]
                forM_ (zip [0 ..] $ Checkpoint.start listingBound [] graph : map snd entries) $ \(cut, checkpoint) ->
                    map fst <$> Checkpoint.resume checkpoint graph [] `shouldBe` Right (drop cut $ map fst entries)
        it "rejects an edited graph as stale" $ do
            let graph = automaton "s" deadRow
                edited = either (error . show) id $ FTA.replaceRows (Map.singleton "q" $ Just [node "n" ["leaf"]]) graph
                checkpoint = Checkpoint.start listingBound [] graph
            void (Checkpoint.resume checkpoint edited []) `shouldBe` Left (StaleRow "q")
            void (Checkpoint.resume checkpoint (automaton "q" deadRow) []) `shouldBe` Left (StaleStart "s" "q")
        it "rejects another route and another version of the route" $ do
            let graph = automaton "s" binary
                checkpoint = Checkpoint.start 3 [] graph
            void (Checkpoint.resume checkpoint{checkpointVersion = 2} graph []) `shouldBe` Left (UnknownRoute Checkpoint.route 2)
            void (Checkpoint.resume checkpoint{checkpointRoute = Text.pack "other"} graph [])
                `shouldBe` Left (UnknownRoute (Text.pack "other") 1)
        it "rejects a position outside the listing" $ do
            -- Up to size three, one binary tree has size one and one has size three.
            let graph = automaton "s" binary
                from next = map fst <$> Checkpoint.resume (Checkpoint.start 3 [] graph){checkpointNext = next} graph []
            forM_ [(0, 0), (1, -1), (1, 2), (2, 1), (4, 1)] $ \next@(size, rank) ->
                from next `shouldBe` Left (OutsideListing size rank)
            from (1, 1) `shouldBe` Right [term "g" [term "a" [], term "a" []]]
            from (2, 0) `shouldBe` Right [term "g" [term "a" [], term "a" []]]
            from (3, 1) `shouldBe` Right []
            from (4, 0) `shouldBe` Right []
        it "relocates a term, and resuming gives the term" $ do
            let graph = automaton "s" deadRow
                edit row = either (error . show) id $ FTA.replaceRows (Map.singleton "q" $ Just row) graph
                added = edit [node "n" ["leaf"], node "m" ["leaf"]]
                checkpoint = Checkpoint.start listingBound [] graph
                firstAfter target found = take 1 . map fst <$> (Checkpoint.relocate checkpoint target [] found >>= \saved -> Checkpoint.resume saved target [])
            forM_ [graph, added] $ \target ->
                forM_ (map fst $ listing target) $ \found -> firstAfter target found `shouldBe` Right [found]
            let removed = term "f" [term "m" [term "k" []]]
                larger = term "g" [term "a" [], term "g" [term "a" [], term "a" []]]
            void (Checkpoint.relocate checkpoint (edit [node "n" ["leaf"]]) [] removed) `shouldBe` Left (MissingTerm removed)
            void (Checkpoint.relocate (Checkpoint.start 3 [] $ automaton "s" binary) (automaton "s" binary) [] larger)
                `shouldBe` Left (MissingTerm larger)
        it "lists the terms of the graph that no exclusion rejects, and resumes at every cut" $
            forM_ listings $ \graph -> do
                let first = Checkpoint.start listingBound someExclusions graph
                    entries = either (error . show) id $ Checkpoint.resume first graph someExclusions
                sort (map fst entries) `shouldBe` sort (filter kept $ map fst $ listing graph)
                forM_ (zip [0 ..] $ first : map snd entries) $ \(cut, checkpoint) ->
                    map fst <$> Checkpoint.resume checkpoint graph someExclusions `shouldBe` Right (drop cut $ map fst entries)

        it "rejects other exclusions as stale, and relocates only to a term that no exclusion rejects" $ do
            let graph = automaton "s" binary
                checkpoint = Checkpoint.start listingBound someExclusions graph
                rejected = term "g" [term "a" [], term "a" []]
                -- A first child of g must not be a, so the only binary tree left is the leaf.
                allowed = term "a" []
            void (Checkpoint.resume checkpoint graph []) `shouldBe` Left StaleExclusions
            void (Checkpoint.resume checkpoint graph $ reverse someExclusions) `shouldBe` Left StaleExclusions
            void (Checkpoint.relocate checkpoint graph someExclusions rejected) `shouldBe` Left (MissingTerm rejected)
            fmap
                (take 1 . map fst)
                (Checkpoint.relocate checkpoint graph someExclusions allowed >>= \saved -> Checkpoint.resume saved graph someExclusions)
                `shouldBe` Right [allowed]

        it "saves a position in a language, and relocates a term into the edited language" $ do
            let language = Language.fromDocument $ either (error . show) id $ Source.fromGraph $ automaton "s" binary
                edit before = either (error . Language.explainUpdateError) id . Language.update before
                aFirst = Anywhere $ TemplateNode (sym "g") [TemplateNode (sym "a") [], Hole]
                excluded = edit language $ Language.without (Language.ExclusionName $ Text.pack "a-first") aFirst
                renamed = edit excluded $ Language.define (Language.at "s" $ Language.ProductionName $ Text.pack "t0") (sym "b") []
                graphOf current = Source.compileGraph $ Language.source current
                exclusionsOf current = Map.elems $ Language.exclusions current
                checkpoint = Checkpoint.start listingBound (exclusionsOf excluded) (graphOf excluded)
                resumeIn current saved = map fst <$> Checkpoint.resume saved (graphOf current) (exclusionsOf current)
                compiled = Language.compileGraph excluded
            fmap sort (resumeIn excluded checkpoint)
                `shouldBe` Right
                    (sort $ map fst $ either (error . show) id $ Checkpoint.resume (Checkpoint.start listingBound [] compiled) compiled [])
            void (resumeIn language checkpoint) `shouldBe` Left StaleExclusions
            void (resumeIn renamed checkpoint) `shouldBe` Left (StaleRow "s")
            fmap
                (take 1)
                (Checkpoint.relocate checkpoint (graphOf renamed) (exclusionsOf renamed) (term "b" []) >>= resumeIn renamed)
                `shouldBe` Right [term "b" []]

        it "rejects a guard beyond equality constraints" $ do
            let different = semanticConstraint $ Not $ Same (ECTA.path [0]) (ECTA.path [1])
                graph = automaton "s" [("s", [FTA.Transition (sym "g") ["q", "q"] different]), ("q", [leaf "a", leaf "b"])]
                checkpoint = Checkpoint.start 3 [] graph
            void (Checkpoint.resume checkpoint graph []) `shouldBe` Left (QueryFailed ResidualGuard)
            void (Checkpoint.relocate checkpoint graph [] $ term "g" [term "a" [], term "b" []])
                `shouldBe` Left (QueryFailed ResidualGuard)
    describe "Data.CFTA.Sized.Checkpoint, sampling" $ do
        it "gives the words of splitmix64.c"
            $
            -- The first three words of the reference splitmix64.c of Sebastiano
            -- Vigna (https://prng.di.unimi.it/splitmix64.c), compiled and run
            -- with its state x set to each seed. The last seed is also the
            -- test of SplitMix64 in the Rust crate rand_xoshiro.
            forM_
                [ (0, [16294208416658607535, 7960286522194355700, 487617019471545679])
                , (1, [10451216379200822465, 13757245211066428519, 17911839290282890590])
                , (42, [13679457532755275413, 2949826092126892291, 5139283748462763858])
                , (maxBound, [16490336266968443936, 16834447057089888969, 4048727598324417001])
                , (1477776061723855037, [1985237415132408290, 2979275885539914483, 13511426838097143398])
                ]
            $ \(seed, expected) -> take 3 (Checkpoint.splitMix64 seed) `shouldBe` expected
        it "draws as the documentation of the module says" $
            -- Uniform runs with 9 terms (one word and rejection) and with more
            -- than 2^64 terms (two words), and a weighted run.
            forM_ [(7, Nothing), (81, Nothing), (7, Just $ Map.fromList [(1, 1), (2, 4), (5, 3)])] $ \(bound, weights) ->
                forM_ [0, 1, 42] $ \seed -> do
                    let graph = automaton "s" binary
                        classes = either (error . show) id $ sized graph
                        run =
                            either (error . show) id $
                                Checkpoint.resumeSampling (Checkpoint.startSampling bound weights seed [] graph) graph weights []
                    forM_ (zip [0 .. 19] run) $ \(index, (found, _)) ->
                        rankOfSize classes found `shouldBe` Just (documentedDraw classes bound weights seed index)
        it "resumes at every cut as the run without a cut"
            $ forM_
                [(graph, weights) | graph <- filter (/= automaton "e" [("e", [])]) listings, weights <- [Nothing, Just sizeWeights]]
            $ \(graph, weights) -> do
                let entries = take 40 $ sampled weights graph
                    run = map fst entries
                forM_ (zip [0 ..] $ Checkpoint.startSampling listingBound weights 7 [] graph : map snd entries) $ \(cut, checkpoint) ->
                    (take cut run <>) . take (40 - cut) . map fst <$> Checkpoint.resumeSampling checkpoint graph weights []
                        `shouldBe` Right run
        it "draws from a listing with more terms than a word counts" $ do
            -- The binary trees with 40 inner nodes alone are more than 2^64.
            let graph = automaton "s" binary
                classes = either (error . show) id $ sized graph
                run =
                    either (error . show) id $ Checkpoint.resumeSampling (Checkpoint.startSampling 81 Nothing 7 [] graph) graph Nothing []
                resumed = either (error . show) id $ Checkpoint.resumeSampling (snd $ run !! 9) graph Nothing []
            sum [count | size <- [1 .. 81], let Cardinality count = countOfSize classes size]
                `shouldSatisfy` (> 2 ^ (64 :: Int))
            forM_ (take 20 run) $ \(found, _) -> fmap fst (rankOfSize classes found) `shouldSatisfy` maybe False (<= 81)
            map fst (take 10 resumed) `shouldBe` map fst (take 10 $ drop 10 run)
        it "gives each term of the listing the same chance without weights" $ do
            -- Up to size seven, nine binary trees.
            let graph = automaton "s" binary
                listed = concatMap (termsOfSize $ either (error . show) id $ sized graph) [1 .. listingBound]
                counts = Map.fromListWith (+) [(found, 1 :: Int) | found <- map fst $ take 9000 $ sampled Nothing graph]
            Map.keys counts `shouldBe` sort listed
            Map.elems counts `shouldSatisfy` all (\count -> count > 850 && count < 1150)
        it "selects a size by its weight, then each term of that size with the same chance" $ do
            -- Size two has no terms, so sizes one and five have the chances one in four and three in four.
            let graph = automaton "s" binary
                weights = Just $ Map.fromList [(1, 1), (2, 4), (5, 3)]
                counts = Map.fromListWith (+) [(found, 1 :: Int) | found <- map fst $ take 4000 $ sampled weights graph]
            map length (Map.keys counts) `shouldBe` [1, 5, 5]
            Map.elems counts `shouldSatisfy` all (\count -> count > 850 && count < 1150) . take 1
            Map.elems counts `shouldSatisfy` all (\count -> count > 1350 && count < 1650) . drop 1
        it "draws only terms that no exclusion rejects, and resumes at every cut" $ do
            let graph = automaton "s" binary
                start = Checkpoint.startSampling listingBound Nothing 7 someExclusions graph
                entries = take 40 $ either (error . show) id $ Checkpoint.resumeSampling start graph Nothing someExclusions
                run = map fst entries
            take 400 (map fst $ either (error . show) id $ Checkpoint.resumeSampling start graph Nothing someExclusions)
                `shouldSatisfy` all kept
            forM_ (zip [0 ..] $ start : map snd entries) $ \(cut, checkpoint) ->
                (take cut run <>) . take (40 - cut) . map fst <$> Checkpoint.resumeSampling checkpoint graph Nothing someExclusions
                    `shouldBe` Right run
            void (Checkpoint.resumeSampling start graph Nothing []) `shouldBe` Left StaleExclusions

        it "rejects an edited graph, other weights, another generator, and another route" $ do
            let graph = automaton "s" deadRow
                edited = either (error . show) id $ FTA.replaceRows (Map.singleton "q" $ Just [node "n" ["leaf"]]) graph
                checkpoint = Checkpoint.startSampling listingBound Nothing 7 [] graph
                from saved target weights = void $ Checkpoint.resumeSampling saved target weights []
            from checkpoint edited Nothing `shouldBe` Left (StaleRow "q")
            from checkpoint graph (Just sizeWeights) `shouldBe` Left StaleWeights
            from checkpoint{samplingPrngVersion = 2} graph Nothing `shouldBe` Left (UnknownPrng Checkpoint.prng 2)
            from checkpoint{samplingVersion = 2} graph Nothing `shouldBe` Left (UnknownRoute Checkpoint.sampleRoute 2)
        it "rejects invalid weights, a listing with nothing to draw, and a negative number of draws" $ do
            let graph = automaton "s" binary
                from weights target = void $ Checkpoint.resumeSampling (Checkpoint.startSampling listingBound weights 7 [] target) target weights []
                weighted = Just . Map.fromList
            from (weighted [(2, 0)]) graph `shouldBe` Left (InvalidWeight 2 0)
            from (weighted [(0, 1)]) graph `shouldBe` Left (InvalidWeight 0 1)
            from (weighted [(listingBound + 1, 1)]) graph `shouldBe` Left (InvalidWeight (listingBound + 1) 1)
            from (weighted [(2, 1)]) graph `shouldBe` Left NothingToDraw
            from Nothing (automaton "e" [("e", [])]) `shouldBe` Left NothingToDraw
            void
                ( Checkpoint.resumeSampling
                    (Checkpoint.startSampling listingBound Nothing 7 [] graph){samplingDraws = -1}
                    graph
                    Nothing
                    []
                )
                `shouldBe` Left (InvalidDraws (-1))
        it "rejects a guard beyond equality constraints" $ do
            let different = semanticConstraint $ Not $ Same (ECTA.path [0]) (ECTA.path [1])
                graph = automaton "s" [("s", [FTA.Transition (sym "g") ["q", "q"] different]), ("q", [leaf "a", leaf "b"])]
            void (Checkpoint.resumeSampling (Checkpoint.startSampling 3 Nothing 7 [] graph) graph Nothing [])
                `shouldBe` Left (QueryFailed ResidualGuard)

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

{- | 'sizedStates' gives, for each state that the initial state reaches, the
classes that 'sized' gives with that state as the initial state.
-}
stateAgreement :: SizedAutomaton -> Property
stateAgreement (SizedAutomaton description) =
    counterexample (show description)
        $ QC.within 5000000
        $ QC.conjoin
            [ counterexample ("state " <> show state <> ", size " <> show size) $
                termsOfSize shared (Size size) === termsOfSize alone (Size size)
                    .&&. countOfSize shared (Size size) === countOfSize alone (Size size)
                    .&&. [unrankOfSize shared (Size size) (ClassRank rank) | rank <- ranks]
                        === [unrankOfSize alone (Size size) (ClassRank rank) | rank <- ranks]
                    .&&. map (rankOfSize shared) (termsOfSize alone (Size size))
                        === map (rankOfSize alone) (termsOfSize alone (Size size))
            | state <- Map.keys $ FTA.transitionTable $ FTA.trim graph
            , let shared = states state
                  alone = either (error . show) id $ sized $ either (error . show) id $ FTA.mkFTA state rows
            , size <- [1 .. sizeBound]
            , let Cardinality count = countOfSize alone (Size size)
                  ranks = [-1 .. count]
            ]
  where
    graph = either (error . show) id $ toFTA $ automatonNode description
    rows = Map.toList $ FTA.transitionTable graph
    states = either (error . show) id $ sizedStates graph

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

-- | Exclusions at the root and anywhere, with a hole: no root @f@ with one child, and no @g@ whose first child is @a@.
someExclusions :: [Exclusion Symbol]
someExclusions = [AtRoot (TemplateNode (sym "f") [Hole]), Anywhere (TemplateNode (sym "g") [TemplateNode (sym "a") [], Hole])]

-- | Whether no exclusion of 'someExclusions' rejects a term.
kept :: Term Symbol -> Bool
kept found =
    matchesNone [template | AtRoot template <- someExclusions] found
        && matchesNowhere [template | Anywhere template <- someExclusions] found

-- | The largest size of the listings of the checkpoint tests.
listingBound :: Size
listingBound = 7

-- | The listing of the terms of a graph up to 'listingBound', each with the checkpoint after it.
listing :: FTA.FTA String Symbol Constraint -> [(Term Symbol, Checkpoint String)]
listing graph = either (error . show) id $ Checkpoint.resume (Checkpoint.start listingBound [] graph) graph []

{- | Graphs with recursion, empty size classes, a dead and a repeated
transition, and equality constraints, and a graph without terms.
-}
listings :: [FTA.FTA String Symbol Constraint]
listings =
    [ automaton "s" binary
    , automaton "s" deadRow
    , automaton
        "s"
        [ ("s", [node "f" ["p", "r"], node "f" ["q", "t"]])
        , ("p", [leaf "a", leaf "a", leaf "z"])
        , ("q", [leaf "a", leaf "m"])
        , ("r", [leaf "r"])
        , ("t", [leaf "t"])
        ]
    , automaton "s" [("s", [leaf "a", leaf "b", FTA.Transition (sym "g") ["s", "s"] equalChildren, node "f" ["s"]])]
    , automaton "e" [("e", [])]
    ]
  where
    equalChildren = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]

{- | The size and class rank of draw @i@, by the steps in the documentation of
"Data.CFTA.Sized.Checkpoint", with only 'Checkpoint.splitMix64'.
-}
documentedDraw :: Sized Symbol -> Size -> Maybe (Map.Map Size Weight) -> Word64 -> Integer -> (Size, ClassRank)
documentedDraw classes bound weights seed index = case weights of
    Nothing ->
        let (rank, _) = value (sum $ map snd counts) stream
         in locate rank counts
    Just weighted ->
        let drawn = [(size, weight) | (size, Weight weight) <- Map.toAscList weighted, count size > 0]
            (ticket, rest) = value (sum $ map snd drawn) stream
            (selected, _) = locate ticket drawn
         in (selected, ClassRank $ fst $ value (count selected) rest)
  where
    count size = let Cardinality total = countOfSize classes size in total
    counts = [(size, count size) | size <- [1 .. bound]]
    stream = Checkpoint.splitMix64 $ Checkpoint.splitMix64 seed !! fromInteger index
    -- The value below a bound, with the words that it reads.
    value 1 input = (0, input)
    value n input =
        let bits = length $ takeWhile (\b -> 2 ^ b <= n - 1) [0 :: Int ..]
            k = (bits + 63) `div` 64
            (taken, rest) = splitAt k input
            v = sum [toInteger u * 2 ^ (64 * j) | (j, u) <- zip [0 :: Int ..] taken] `mod` 2 ^ bits
         in if v < n then (v, rest) else value n rest
    -- The entry whose range of values holds the value, and the place in that range.
    locate v ((size, width) : later)
        | v < width = (size, ClassRank v)
        | otherwise = locate (v - width) later
    locate _ [] = error "a value beyond the last range"

-- | The run of draws from the listing of a graph up to 'listingBound', with seed seven.
sampled :: Maybe (Map.Map Size Weight) -> FTA.FTA String Symbol Constraint -> [(Term Symbol, SamplingCheckpoint String)]
sampled weights graph =
    either (error . show) id $
        Checkpoint.resumeSampling (Checkpoint.startSampling listingBound weights 7 [] graph) graph weights []

-- | Weights of sizes up to 'listingBound', with a size of no terms in some listings.
sizeWeights :: Map.Map Size Weight
sizeWeights = Map.fromList [(1, 1), (3, 2), (6, 1), (7, 5)]

-- | Binary trees: a leaf, or a node with two trees.
binary :: [(String, [FTA.Transition String Symbol Constraint])]
binary = [("s", [leaf "a", node "g" ["s", "s"]])]

-- | Rows with a dead transition: the child state of @a@ has no transitions.
deadRow :: [(String, [FTA.Transition String Symbol Constraint])]
deadRow =
    [ ("s", [node "f" ["p"], node "f" ["q"]])
    , ("p", [node "a" ["dead"], node "z" ["leaf"]])
    , ("q", [node "m" ["leaf"]])
    , ("leaf", [leaf "k"])
    , ("dead", [])
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
