module Data.CFTA.Gen.Refinement.StateMachineTraceSpec (spec) where

import Data.List (sort)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.StateMachineTraceLanguage
import Data.CFTA.Gen.Refinement.TestSupport (ranks, termsOf, values)
import qualified Data.CFTA.Gen.Refinement.TestSupport as Support
import Data.CFTA.Index (Cardinality (..), Rank (..))
import Data.CFTA.Refinement (Symbol (RefinedSymbol))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Assuming)
import qualified Data.CFTA.Term as Term

-- | Compile one trace language with the symbolic model environment.
compileOrFail :: LTAGen.LTAGen a -> IO (LTAGen.LTAGen a)
compileOrFail generator =
    withZ3Assuming [] solverAssumptions $ \solver ->
        Support.compileOrFail solver generator

-- | Compile the automaton-level flagship path with the symbolic model.
compileTraceOrFail :: Int -> IO (LTAGen.LTAGen Trace)
compileTraceOrFail traceLength =
    withZ3Assuming [] solverAssumptions $ \solver -> do
        compileTracesOfLength solver traceLength >>= Support.rightOrFail

spec :: Spec
spec =
    describe "liquid typed stack-machine traces" $ do
        it "prelinks the liquid transition relation and preserves the automaton's annotated ranks" $
            withZ3Assuming [] solverAssumptions $ \solver -> do
                table <- deriveTraceTransitions solver >>= Support.rightOrFail
                let states = [StackState types | n <- [0 .. maximumStackDepth], types <- sequence $ replicate n [TInt, TBool]]
                    commands = map Push [IntValue 0, IntValue 1, BoolValue False, BoolValue True] <> [Add, And, Equal, Not, Pop]
                    expected =
                        [ (input, command, after)
                        | input <- Nothing : map Just states
                        , command <- commands
                        , Just (_, after) <- [modelStep (maybe (StackState []) id input) command]
                        ]
                sort (traceTransitionRows table) `shouldBe` sort expected
                let checkRanks n = do
                        old <- compileTraceAutomaton solver n >>= Support.rightOrFail
                        linked <- Support.rightOrFail $ prelinkedTraces table n
                        LTAGen.cardinality old `shouldBe` Right (Cardinality $ traceCount n (StackState []))
                        LTAGen.cardinality linked `shouldBe` LTAGen.cardinality old
                        expectedValues <- Support.rightOrFail $ traverse (LTAGen.unrank old) (ranks old)
                        expectedTerms <- Support.rightOrFail $ traverse (Support.termOf old) (ranks old)
                        traverse (LTAGen.unrank linked) (ranks old) `shouldBe` Right expectedValues
                        traverse (Support.termOf linked) (ranks old) `shouldBe` Right expectedTerms
                mapM_ checkRanks [0 .. 3]
                old <- compileTraceAutomaton solver 6 >>= Support.rightOrFail
                linked <- Support.rightOrFail $ prelinkedTraces table 6
                let count = traceCount 6 (StackState [])
                    probes = map Rank [0, count `div` 3, count `div` 2, count - 1]
                LTAGen.cardinality linked `shouldBe` Right (Cardinality count)
                expectedTerms <- Support.rightOrFail $ traverse (Support.termOf old) probes
                traverse (Support.termOf linked) probes `shouldBe` Right expectedTerms
        it "reuses finite transition decisions across lengths and preserves every small rank" $
            withZ3Assuming [] solverAssumptions $ \solver -> do
                family <- compileTracesThrough solver 4 >>= Support.rightOrFail
                separate <- traverse (\n -> compileTracesOfLength solver n >>= Support.rightOrFail) [0 .. 4]
                let compiled = LTAGen.familyGenerators family
                map values compiled `shouldBe` map values separate
                map termsOf compiled `shouldBe` map termsOf separate
                map LTAGen.cardinality compiled
                    `shouldBe` [Right $ Cardinality $ traceCount n (StackState []) | n <- [0 .. 4]]
                LTAGen.transitionDecisions family `shouldSatisfy` (> 0)
                LTAGen.transitionReuses family `shouldSatisfy` (> 0)

        it "matches the independent trace counts through length four" $ do
            compiled <- traverse compileTraceOrFail [1 .. 4]
            map LTAGen.cardinality compiled
                `shouldBe` [Right $ Cardinality $ traceCount length_ (StackState []) | length_ <- [1 .. 4]]

        it "keeps the independent trace counts through length ten" $
            -- These constants are the values traceCount produced when the
            -- trace grammar was fixed. They lock the grammar; the compiled
            -- languages agree with traceCount for lengths one to four above
            -- and for length ten below.
            [traceCount length_ (StackState []) | length_ <- [1 .. 10]]
                `shouldBe` [4, 22, 132, 556, 3104, 13760, 73528, 342136, 1783112, 8567224]

        it "compiles the qualified-do surface at length ten" $ do
            compiled <- compileTraceOrFail 10
            LTAGen.cardinality compiled `shouldBe` Right (Cardinality $ traceCount 10 (StackState []))

        it "retains valid structural shrinks from the relational ECTA plan" $ do
            compiled <- compileTraceOrFail 3
            let candidates =
                    [ candidate
                    | source <- ranks compiled
                    , candidate <- LTAGen.shrinkRank compiled source
                    ]
            candidates `shouldSatisfy` not . null
            candidates `shouldSatisfy` all (`elem` ranks compiled)
            let shrunk =
                    [ member
                    | candidate <- candidates
                    , Right member <- [LTAGen.unrank compiled candidate]
                    ]
            shrunk `shouldSatisfy` all traceIsValid

        it "compiles the hand-built trace automaton to the same language" $
            withZ3Assuming [] solverAssumptions $ \solver -> do
                automaton <- compileTraceAutomaton solver 4 >>= Support.rightOrFail
                surface <- compileTracesOfLength solver 4 >>= Support.rightOrFail
                LTAGen.cardinality automaton `shouldBe` LTAGen.cardinality surface
                Set.fromList (values automaton) `shouldBe` Set.fromList (values surface)

        it "retains the dependent command sequences and rejects ill-typed ones" $ do
            compiled <- compileTraceOrFail 3
            LTAGen.cardinality compiled `shouldBe` Right 132
            LTAGen.cardinality compiled `shouldBe` Right (Cardinality $ traceCount 3 (StackState []))
            let sequences = Set.fromList $ map (map eventCommand . traceEvents) $ values compiled
            sequences `shouldSatisfy` Set.member [Push (IntValue 0), Push (IntValue 1), Add]
            sequences `shouldSatisfy` Set.member [Push (BoolValue False), Push (BoolValue True), And]
            sequences `shouldSatisfy` Set.member [Push (IntValue 0), Push (IntValue 1), Equal]
            sequences `shouldSatisfy` Set.member [Push (BoolValue False), Not, Pop]
            sequences `shouldSatisfy` not . Set.member [Push (IntValue 0), Not, Pop]
            sequences `shouldSatisfy` not . Set.member [Push (IntValue 0), Push (BoolValue True), Add]

        it "predicts every response and post-state before concrete execution" $ do
            compiled <- compileTraceOrFail 3
            values compiled `shouldSatisfy` all traceIsValid

        it "carries the final stack type as the trace result refinement" $ do
            compiled <- compileTraceOrFail 3
            zip (values compiled) (termsOf compiled)
                `shouldSatisfy` all
                    ( \(trace, term) ->
                        let RefinedSymbol _ refinement = Term.rootLabel term
                         in refinement == stateRefinement (traceFinalState trace)
                    )

        it "shrinks to smaller traces, some shorter, whose stack preconditions still hold" $ do
            compiled <- compileOrFail $ tracesUpTo 3
            let ranked = zip (ranks compiled) (values compiled)
                lengthThreeRanks =
                    [ rank
                    | (rank, trace) <- ranked
                    , length (traceEvents trace) == 3
                    ]
            case lengthThreeRanks of
                source : _ -> do
                    let shrunk = map LTAGen.rankedValue $ LTAGen.smallerMembers compiled source
                    shrunk `shouldSatisfy` any ((< 3) . length . traceEvents)
                    shrunk `shouldSatisfy` all traceIsValid
                [] -> expectationFailure "no accepted three-step trace"

        it "gives QuickCheck a precondition-free property over valid traces" $ do
            compiled <- compileOrFail $ tracesUpTo 3
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSuccess = 200} $
                    LTAGen.forAll compiled $ \trace ->
                        QC.counterexample (show trace) $
                            replayTrace trace QC.=== Just (traceFinalState trace)
            QC.isSuccess result `shouldBe` True

        modifyMaxSuccess (const 300)
            $ it "keeps every reference generator in the valid trace language"
            $ QC.conjoin
                [ QC.forAll (generator 4) $ \trace ->
                    QC.counterexample (show trace) $
                        QC.conjoin
                            [ QC.property $ traceIsValid trace
                            , length (traceEvents trace) QC.=== 4
                            ]
                | generator <-
                    [ naiveTraceGen
                    , qsmTraceGen
                    , handwrittenTraceGen
                    , rankedTraceGen
                    ]
                ]

        it "replays every QSM-style deletion shrink through the model" $
            QC.forAll (qsmTraceGen 8) $ \trace ->
                QC.counterexample (show trace) $
                    QC.conjoin
                        [ QC.property $ traceIsValid shrunk
                        | shrunk <- qsmTraceShrinks trace
                        ]
