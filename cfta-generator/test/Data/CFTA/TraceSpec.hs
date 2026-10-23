module Data.CFTA.TraceSpec (spec) where

import Control.Monad (foldM, forM_, replicateM)
import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable)
import Data.List (sort)
import GHC.Generics (Generic)
import Test.Hspec (Expectation, Spec, describe, it, shouldBe)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Gen as Gen
import qualified Data.CFTA.Gen.Refinement.StateMachineTraceLanguage as Typed
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size (..), everyRank)
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Lowering (Expansion (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Sized (Sized, countOfSize, rankOfSize, sized, termsOfSize, unrankOfSize)
import Data.CFTA.Template (excludePrefixesFTA)
import Data.CFTA.Trace

-- | The steps of a stack of plain values.
data StackStep = Push | Add | Pop
    deriving (Bounded, Enum, Eq, Ord, Show, Generic)

instance Hashable StackStep

-- | A stack of at most the given depth. The state is the depth.
stack :: Int -> Description Int StackStep
stack bound = Description 0 [minBound .. maxBound] next (const True)
  where
    next depth Push | depth < bound = Just (depth + 1)
    next depth Add | depth >= 2 = Just (depth - 1)
    next depth Pop | depth >= 1 = Just (depth - 1)
    next _ _ = Nothing

-- | The state of a file handle.
data Handle = Closed | Opened
    deriving (Eq, Ord, Show)

-- | The steps of a file handle, and two steps of a finer alphabet that lower to 'Read'.
data HandleStep = Open | Read | Close | ReadLine | ReadByte
    deriving (Eq, Ord, Show, Generic)

instance Hashable HandleStep

-- | A file handle: it reads and closes only when it is open.
handle :: Description Handle HandleStep
handle = Description Closed [Open, Read, Close] next (const True)
  where
    next Closed Open = Just Opened
    next Opened Read = Just Opened
    next Opened Close = Just Closed
    next _ _ = Nothing

-- | At most two reads. The state is the number of reads.
atMostTwoReads :: Description Int HandleStep
atMostTwoReads = Description 0 [Open, Read, Close] next (const True)
  where
    next count Read = if count < 2 then Just (count + 1) else Nothing
    next count _ = Just count

-- | The steps of a bank account.
data AccountStep = Deposit Int | Withdraw Int
    deriving (Eq, Ord, Show)

-- | A bank account: it withdraws only an amount that the balance allows. The state is the balance, which has no bound.
account :: Description Int AccountStep
account = Description 0 [Deposit 1, Deposit 2, Withdraw 1, Withdraw 2] next (const True)
  where
    next balance (Deposit amount) = Just (balance + amount)
    next balance (Withdraw amount) = if amount <= balance then Just (balance - amount) else Nothing

-- | The traces of a description with at most the given number of steps. The state counts the steps.
unrolled :: Int -> Description state step -> Description (Int, state) step
unrolled bound Description{descriptionInitial, descriptionSteps, descriptionNext, descriptionFinal} =
    Description (0, descriptionInitial) descriptionSteps next (descriptionFinal . snd)
  where
    next (count, state) step
        | count < bound = (count + 1,) <$> descriptionNext state step
        | otherwise = Nothing

-- | Every sequence of the steps.
free :: [step] -> Description () step
free steps = Description () steps (\_ _ -> Just ()) (const True)

-- | Whether a sequence of steps runs and ends in a final state, by the description alone.
runs :: Description state step -> [step] -> Bool
runs Description{descriptionInitial, descriptionNext, descriptionFinal} =
    maybe False descriptionFinal . foldM descriptionNext descriptionInitial

-- | The sequences of steps of a length that run, by brute force.
bruteForce :: Description state step -> Int -> [[step]]
bruteForce description length_ = filter (runs description) $ replicateM length_ $ descriptionSteps description

-- | The size classes of an automaton.
classesOf :: (Ord state, Ord step) => FTA.PlainFTA state (TraceSymbol step) -> Sized (TraceSymbol step)
classesOf = either (error . show) id . sized

-- | The traces of a length that an automaton accepts, in rank order.
tracesOf :: (Ord state, Ord step) => FTA.PlainFTA state (TraceSymbol step) -> Int -> Maybe [[step]]
tracesOf automaton length_ = traverse traceSteps $ termsOfSize (classesOf automaton) (sizeOf length_)

-- | The size of the term of a trace of a length.
sizeOf :: Int -> Size
sizeOf length_ = Size $ fromIntegral length_ + 1

-- | The traces of two automata that both accept.
intersection ::
    (Ord left, Ord right, Ord step) =>
    FTA.PlainFTA left (TraceSymbol step) ->
    FTA.PlainFTA right (TraceSymbol step) ->
    FTA.PlainFTA (FTA.ProductState left right) (TraceSymbol step)
intersection left right =
    either (const $ error "intersection: trace symbols have one arity each") FTA.dropConstraints $ FTA.intersect left right

-- | Check the size class of a length against brute force, and rank each member back.
checkLength :: (Ord state, Ord step, Show step) => Description state step -> Int -> Expectation
checkLength description length_ = do
    let classes = classesOf $ traceAutomaton description
        size = sizeOf length_
        expected = bruteForce description length_
    fmap sort (traverse traceSteps $ termsOfSize classes size) `shouldBe` Just (sort expected)
    countOfSize classes size `shouldBe` Cardinality (fromIntegral $ length expected)
    let Cardinality count = countOfSize classes size
    forM_ [0 .. count - 1] $ \rank ->
        (rankOfSize classes =<< unrankOfSize classes size (ClassRank rank)) `shouldBe` Just (size, ClassRank rank)

-- | Check 'feasibility' on a sequence against a run of the description.
checkFeasibility :: (Ord state, Show state, Ord step, Show step) => Description state step -> [step] -> Expectation
checkFeasibility description@Description{descriptionInitial, descriptionNext, descriptionFinal} steps =
    case feasibility (traceAutomaton description) steps of
        Right states -> do
            runs description steps `shouldBe` True
            Just states `shouldBe` (pure <$> foldM descriptionNext descriptionInitial steps)
        Left (Infeasible done symbol states) -> do
            runs description steps `shouldBe` False
            -- The steps before the failure run, and the next symbol fails in the state after them.
            let after = foldM descriptionNext descriptionInitial done
            take (length done) steps `shouldBe` done
            (pure <$> after) `shouldBe` Just states
            case symbol of
                Step step -> do
                    take 1 (drop (length done) steps) `shouldBe` [step]
                    ((`descriptionNext` step) <$> after) `shouldBe` Just Nothing
                End -> do
                    length done `shouldBe` length steps
                    (descriptionFinal <$> after) `shouldBe` Just False

spec :: Spec
spec = describe "Data.CFTA.Trace" $ do
    it "lists, counts, and ranks the traces of each length as brute force does" $
        forM_ [0 .. 7] $ \length_ -> do
            checkLength (stack 3) length_
            checkLength handle length_
            checkLength handle{descriptionInitial = Opened} length_
            checkLength handle{descriptionFinal = (== Closed)} length_
    it "samples and shrinks only traces whose preconditions hold" $ do
        let generator = Gen.upToSize (sizeOf 6) $ Gen.fromAutomaton $ fromFTA $ traceAutomaton $ stack 3
            total = either (error . show) id $ Gen.cardinality generator
        total `shouldBe` Cardinality (fromIntegral $ sum [length $ bruteForce (stack 3) length_ | length_ <- [0 .. 6]])
        forM_ (everyRank total) $ \rank ->
            forM_ (rank : Gen.shrinkRank generator rank) $ \candidate ->
                (fmap (runs $ stack 3) . traceSteps <$> Gen.unrank generator candidate) `shouldBe` Right (Just True)
    it "counts the typed stack traces of the trace benchmark language" $ do
        let empty = Typed.StackState []
            commands =
                map Typed.Push [Typed.IntValue 0, Typed.IntValue 1, Typed.BoolValue False, Typed.BoolValue True]
                    <> [Typed.Add, Typed.And, Typed.Equal, Typed.Not, Typed.Pop]
            typed = Description empty commands (\state command -> snd <$> Typed.modelStep state command) (const True)
            classes = classesOf $ traceAutomaton typed
        forM_ [0 .. 8] $ \length_ ->
            countOfSize classes (sizeOf length_) `shouldBe` Cardinality (Typed.traceCount length_ empty)
    it "gives the shortest prefix that has no run and the state in which its last symbol fails" $ do
        feasibility (traceAutomaton handle) [Open, Read, Close] `shouldBe` Right [Closed]
        feasibility (traceAutomaton handle) [Open, Read, Close, Read, Open]
            `shouldBe` Left (Infeasible [Open, Read, Close] (Step Read) [Closed])
        feasibility (traceAutomaton $ stack 3) [Push, Push, Add, Add, Pop]
            `shouldBe` Left (Infeasible [Push, Push, Add] (Step Add) [1])
        feasibility (traceAutomaton handle{descriptionFinal = (== Closed)}) [Open, Read]
            `shouldBe` Left (Infeasible [Open, Read] End [Opened])
        forM_ [0 .. 5] $ \length_ -> do
            mapM_ (checkFeasibility $ stack 2) $ replicateM length_ [minBound .. maxBound]
            mapM_ (checkFeasibility handle{descriptionFinal = (== Closed)}) $ replicateM length_ [Open, Read, Close]
    it "intersects two descriptions over one step type" $ do
        let both = intersection (traceAutomaton handle) (traceAutomaton atMostTwoReads)
        forM_ [0 .. 7] $ \length_ ->
            fmap sort (tracesOf both length_) `shouldBe` Just (sort $ filter (runs atMostTwoReads) $ bruteForce handle length_)
        -- The state in which the step fails tells which description rejects it.
        feasibility both [Open, Read, Read, Close, Open, Read]
            `shouldBe` Left (Infeasible [Open, Read, Read, Close, Open] (Step Read) [FTA.ProductState Opened 2])
    it "finds the shortest trace that reads and ends closed" $ do
        let reads_ = Description False [Open, Read, Close] (\seen step -> Just $ seen || step == Read) id
            both = intersection (traceAutomaton handle{descriptionFinal = (== Closed)}) (traceAutomaton reads_)
        (fmap traceSteps <$> Gen.smallest (Gen.fromAutomaton $ fromFTA both)) `shouldBe` Right (Just $ Just [Open, Read, Close])
    it "excludes the shortest failing prefixes from every sequence and gives the traces" $ do
        -- The dead prefixes of a search with an external check: here the check is the description.
        let maximumLength = 6
            steps = [Open, Read, Close]
            failures =
                nubOrd
                    [ done <> [step]
                    | candidate <- replicateM maximumLength steps
                    , Left (Infeasible done (Step step) _) <- [feasibility (traceAutomaton handle) candidate]
                    ]
            learned = excludePrefixesFTA [[(Step step, 1) | step <- failure] | failure <- failures] $ traceAutomaton $ free steps
        forM_ [0 .. maximumLength] $ \length_ ->
            fmap sort (tracesOf learned length_) `shouldBe` Just (sort $ bruteForce handle length_)
    it "unrolls a description with an unbounded state to a length bound" $ do
        let bounded = traceAutomaton $ unrolled 6 account
        forM_ [0 .. 6] $ \length_ -> fmap sort (tracesOf bounded length_) `shouldBe` Just (sort $ bruteForce account length_)
        tracesOf bounded 7 `shouldBe` Just []
    it "lifts the traces to a finer step alphabet with a template lowering" $ do
        let lowering =
                either (error . show) id $
                    Lowering.mkLowering
                        [ (Step ReadLine, 1, Apply (Step Read) [Child 0])
                        , (Step ReadByte, 1, Apply (Step Read) [Child 0])
                        ]
            fine = [Open, ReadLine, ReadByte, Close]
            coarse step = if step `elem` [ReadLine, ReadByte] then Read else step
            lifted = either (error . show) id $ Lowering.lift lowering $ traceAutomaton handle
            fineTraces = intersection (traceAutomaton $ free fine) lifted
            image = either (error . show) id $ FTA.mapSymbols (fmap coarse) fineTraces
        forM_ [0 .. 6] $ \length_ -> do
            fmap sort (tracesOf fineTraces length_)
                `shouldBe` Just (sort [steps | steps <- replicateM length_ fine, runs handle (map coarse steps)])
            fmap sort (tracesOf image length_) `shouldBe` Just (sort $ bruteForce handle length_)
