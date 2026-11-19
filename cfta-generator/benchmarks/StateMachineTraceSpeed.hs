{- | Compare seven exact-uniform generators and one QSM-style baseline.

The naive generator rejects whole raw command sequences, the bespoke generator
tracks exact suffix counts in Haskell, the QSM-style generator chooses a valid
next command from the current model, the ranked control hand-codes one global
rank decoder, and four LTA rows compile the generator surface and the trace
automaton with and without finite transition tables. QSM-style generation
has the same support with a different distribution.
-}
module Main (main) where

import Control.Monad ((>=>))
import Data.List (intercalate, sortOn)
import qualified Data.Text as Text
import System.Environment (getArgs)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.StateMachineTraceLanguage
import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Assuming)
import Data.CFTA.Symbol (symbolText)
import qualified Data.CFTA.Term as Term
import GeneratorSpeedHarness (Benchmark (..), benchmarkMain)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["compiled-stack"] -> withZ3Assuming [] solverAssumptions $ \solver -> do
            table <- deriveTraceTransitions solver >>= either (fail . LTAGen.explain) pure
            exportCompiledStack table
        ["family", engine, bound] -> runFamily engine (read bound)
        _ -> benchmarkMain benchmark

-- | Export the complete decision table, each link order, and small annotated rank streams.
exportCompiledStack :: TraceTransitions -> IO ()
exportCompiledStack table = do
    row $ "schemas" : names
    mapM_ decisions [True, False]
    mapM_ links [True, False]
    mapM_ ranks [0 .. 2]
  where
    (names, blocks) = traceTransitionIndices table
    ordered initial = sortOn fst [(out, edges) | (first, out, edges) <- blocks, initial == first]
    states = map fst $ ordered False
    row = putStrLn . intercalate "\t"
    kind True = "start"
    kind False = "step"
    decisions initial = mapM_ one $ if initial then [0] else states
      where
        one input = row $ [kind initial, show input] <> map (cell input) [0 .. length names - 1]
        cell input choice = case [show out | (out, edges) <- ordered initial, (input, choice) `elem` edges] of
            [] -> "-"
            outputs -> intercalate "," outputs
    links initial =
        mapM_
            ( \(out, edges) -> row $ ["order", kind initial, show out] <> [show input <> "/" <> show choice | (input, choice) <- edges]
            )
            $ ordered initial
    checked result = either (fail . LTAGen.explain) pure result
    ranks n = do
        generator <- checked $ prelinkedTraces table n
        count <- checked $ LTAGen.cardinality generator
        mapM_ (emit generator) $ everyRank count
      where
        emit generator rank = do
            term <- checked $ LTAGen.termAt generator rank
            case LTAGen.surface term of
                [trace] -> do
                    events <- schemas trace
                    row ["rank", show n, intercalate "," events]
                _ -> fail "expected one annotated trace"
    schemas (Term.Node symbol children) = case (Text.unpack (symbolText symbol), children) of
        ("start", []) -> pure []
        ("step", [previous, command]) -> (<> [Text.unpack $ symbolText $ Term.rootLabel command]) <$> schemas previous
        _ -> fail "expected a start or step node"

{- | Compile the same exact-length roots with each engine. Include rank decoding
in the checksum so both runs force the resulting languages.
-}
runFamily :: String -> Int -> IO ()
runFamily engine bound = withZ3Assuming [] solverAssumptions $ \solver -> do
    let checked result = either (fail . LTAGen.explain) pure result
    generators <- case engine of
        "separate" -> traverse (compileTracesOfLength solver >=> checked) [0 .. bound]
        "automaton" -> traverse (compileTraceAutomaton solver >=> checked) [0 .. bound]
        "prelinked" -> do
            table <- deriveTraceTransitions solver >>= checked
            putStrLn $ "accepted-rows=" <> show (length $ traceTransitionRows table)
            traverse (checked . prelinkedTraces table) [0 .. bound]
        "indexed" -> do
            family <- compileTracesThrough solver bound >>= checked
            putStrLn $
                "decisions=" <> show (LTAGen.transitionDecisions family) <> " reuses=" <> show (LTAGen.transitionReuses family)
            pure $ LTAGen.familyGenerators family
        _ -> fail "usage: family (separate|indexed|automaton|prelinked) maximum-length"
    checksum <- traverse (checked . score) generators
    putStrLn $ "counts-and-rank-checksums=" <> show checksum
  where
    score generator = do
        Cardinality n <- LTAGen.cardinality generator
        traces <- traverse (LTAGen.unrank generator . Rank) [0, n `div` 2, n - 1]
        pure (n, map commandSequence traces)
    -- Command codes are distinct and below 32. Keep their order in the signature.
    commandSequence = foldl' (\code event -> code * 32 + toInteger (commandScore $ eventCommand event)) 1 . traceEvents

-- | Typed stack-machine trace benchmark configuration.
benchmark :: Benchmark Trace
benchmark =
    Benchmark
        { benchmarkSizeName = "length"
        , benchmarkSizes = [1 .. 10] <> [12, 16, 20, 30, 40]
        , benchmarkEngines =
            [ "naive"
            , "qsm-online"
            , "bespoke"
            , "ranked"
            , "lta-do"
            , "lta-indexed"
            , "lta-automaton"
            , "lta-prelinked"
            ]
        , benchmarkSampleCount = 20000
        , benchmarkMembers = \length_ -> traceCount length_ (StackState [])
        , benchmarkPrepare = prepare
        , benchmarkTally = traceScore
        }

-- | Construct one selected exact-length generator.
prepare :: String -> Int -> IO (QC.Gen Trace)
prepare "naive" length_ = pure $ naiveTraceGen length_
prepare "qsm-online" length_ = pure $ qsmTraceGen length_
prepare "bespoke" length_ = pure $ handwrittenTraceGen length_
prepare "ranked" length_ = pure $ rankedTraceGen length_
prepare "lta" length_ = prepare "lta-do" length_
prepare engine length_ | engine == "lta-do" || engine == "lta-indexed" =
    withZ3Assuming [] solverAssumptions $ \solver -> do
        result <-
            if engine == "lta-do"
                then compileTracesOfLength solver length_
                else do
                    compiled <- LTAGen.compileFamilyWith solver [tracesOfLength length_]
                    case fmap LTAGen.familyGenerators compiled of
                        Left err -> pure $ Left err
                        Right [generator] -> pure $ Right generator
                        Right _ -> fail "expected one compiled length"
        case result of
            Left err -> fail $ "could not compile LTA benchmark: " <> LTAGen.explain err
            Right compiled
                | LTAGen.cardinality compiled == Right (Cardinality $ traceCount length_ (StackState [])) ->
                    pure $ LTAGen.toGen compiled
                | otherwise -> fail "LTA cardinality differs from the independent trace count"
prepare "lta-automaton" length_ =
    withZ3Assuming [] solverAssumptions $ \solver -> do
        result <- compileTraceAutomaton solver length_
        case result of
            Left err -> fail $ "could not compile the trace automaton: " <> LTAGen.explain err
            Right compiled -> pure $ LTAGen.toGen compiled
prepare "lta-prelinked" length_ =
    withZ3Assuming [] solverAssumptions $ \solver -> do
        table <- deriveTraceTransitions solver
        either (fail . LTAGen.explain) (pure . LTAGen.toGen) $ table >>= (\proved -> prelinkedTraces proved length_)
prepare engine _ = fail $ "unknown engine: " <> engine

-- | Force every trace field and reduce it to a stable checksum contribution.
traceScore :: Trace -> Int
traceScore Trace{traceEvents, traceFinalState} =
    foldl' (\score event -> score + eventScore event) (encodeState traceFinalState) traceEvents

-- | Force and score one predicted transition.
eventScore :: Event -> Int
eventScore Event{eventBefore, eventCommand, eventResponse, eventAfter} =
    encodeState eventBefore
        + commandScore eventCommand
        + responseScore eventResponse
        + encodeState eventAfter

-- | Give every command constructor and pushed value a distinct score.
commandScore :: Command -> Int
commandScore (Push pushed) = 10 + valueScore pushed
commandScore Add = 20
commandScore And = 21
commandScore Equal = 22
commandScore Not = 23
commandScore Pop = 24

-- | Give each literal a distinct score: even for an integer, odd for a Boolean.
valueScore :: Value -> Int
valueScore (IntValue integer) = 2 * integer
valueScore (BoolValue boolean) = if boolean then 3 else 1

-- | Give each predicted response a distinct score.
responseScore :: Response -> Int
responseScore Accepted = 30
responseScore (Popped TInt) = 31
responseScore (Popped TBool) = 32
