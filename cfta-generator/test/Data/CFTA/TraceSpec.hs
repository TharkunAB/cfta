module Data.CFTA.TraceSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM_, replicateM)
import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable)
import Data.List (sort)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import System.Timeout (timeout)
import Test.Hspec (Expectation, Spec, describe, it, shouldBe, shouldReturn)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import qualified Data.CFTA.Gen as Gen
import qualified Data.CFTA.Gen.Refinement.StateMachineTraceLanguage as Typed
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size (..), everyRank)
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Lowering (Expansion (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Sized (Sized, countOfSize, rankOfSize, sized, sizedReference, termsOfSize, unrankOfSize)
import Data.CFTA.Template (excludePrefixesFTA)
import Data.CFTA.Trace

-- | The steps of a stack of plain values.
data StackStep = Push | Add | Pop
    deriving (Bounded, Enum, Eq, Ord, Show, Generic)

instance Hashable StackStep

-- | A stack of at most the given depth. The state is the depth.
stack :: Int -> StateMachine Int StackStep
stack bound = StateMachine 0 [minBound .. maxBound] next (const True)
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
handle :: StateMachine Handle HandleStep
handle = StateMachine Closed [Open, Read, Close] next (const True)
  where
    next Closed Open = Just Opened
    next Opened Read = Just Opened
    next Opened Close = Just Closed
    next _ _ = Nothing

-- | At most two reads. The state is the number of reads.
atMostTwoReads :: StateMachine Int HandleStep
atMostTwoReads = StateMachine 0 [Open, Read, Close] next (const True)
  where
    next count Read = if count < 2 then Just (count + 1) else Nothing
    next count _ = Just count

-- | The steps of a bank account.
data AccountStep = Deposit Int | Withdraw Int
    deriving (Eq, Ord, Show)

-- | A bank account: it withdraws only an amount that the balance allows. The state is the balance, which has no bound.
account :: StateMachine Int AccountStep
account = StateMachine 0 [Deposit 1, Deposit 2, Withdraw 1, Withdraw 2] next (const True)
  where
    next balance (Deposit amount) = Just (balance + amount)
    next balance (Withdraw amount) = if amount <= balance then Just (balance - amount) else Nothing

-- | The traces of a state machine with at most the given number of steps. The state counts the steps.
unrolled :: Int -> StateMachine state step -> StateMachine (Int, state) step
unrolled bound StateMachine{machineInitial, machineSteps, machineNext, machineFinal} =
    StateMachine (0, machineInitial) machineSteps next (machineFinal . snd)
  where
    next (count, state) step
        | count < bound = (count + 1,) <$> machineNext state step
        | otherwise = Nothing

-- | The typed stack of the trace benchmark language.
typedStack :: StateMachine Typed.StackState Typed.Command
typedStack = StateMachine (Typed.StackState []) commands next (const True)
  where
    commands =
        map Typed.Push [Typed.IntValue 0, Typed.IntValue 1, Typed.BoolValue False, Typed.BoolValue True]
            <> [Typed.Add, Typed.And, Typed.Equal, Typed.Not, Typed.Pop]
    next state command = snd <$> Typed.modelStep state command

-- | What a command of the typed stack does, without the types of the values.
data Shape = Pushes | Pops | Combines | Negates
    deriving (Eq, Ord, Show)

-- | The shape of a command of the typed stack.
shape :: Typed.Command -> Shape
shape (Typed.Push _) = Pushes
shape Typed.Pop = Pops
shape Typed.Not = Negates
shape _ = Combines

{- | The automaton of the traces of 'Push' and 'Pop' whose step at the given
place from the end is 'Push'. It has one more state than the place.
-}
pushFromEnd :: Int -> FTA.PlainFTA Int (TraceSymbol StackStep)
pushFromEnd place =
    either (error . show) id
        $ FTA.mkFTA 0
        $ (0, [step Push 0, step Pop 0, step Push 1])
            : [(state, [step Push (state + 1), step Pop (state + 1)]) | state <- [1 .. place - 1]]
                <> [(place, [FTA.Transition End [] noConstraint])]
  where
    step symbol child = FTA.Transition (Step symbol) [child] noConstraint

-- | Every sequence of the steps.
free :: [step] -> StateMachine () step
free steps = StateMachine () steps (\_ _ -> Just ()) (const True)

-- | Whether a sequence of steps runs and ends in a final state, by the state machine alone.
runs :: StateMachine state step -> [step] -> Bool
runs StateMachine{machineInitial, machineNext, machineFinal} =
    maybe False machineFinal . foldM machineNext machineInitial

-- | The sequences of steps of a length that run, by brute force.
bruteForce :: StateMachine state step -> Int -> [[step]]
bruteForce machine length_ = filter (runs machine) $ replicateM length_ $ machineSteps machine

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
    FTA.dropConstraints $ FTA.intersect left right

-- | Check the size class of a length against brute force, and rank each member back.
checkLength :: (Ord state, Ord step, Show step) => StateMachine state step -> Int -> Expectation
checkLength machine length_ = do
    let classes = classesOf $ traceAutomaton machine
        size = sizeOf length_
        expected = bruteForce machine length_
    fmap sort (traverse traceSteps $ termsOfSize classes size) `shouldBe` Just (sort expected)
    countOfSize classes size `shouldBe` Cardinality (fromIntegral $ length expected)
    let Cardinality count = countOfSize classes size
    forM_ [0 .. count - 1] $ \rank ->
        (rankOfSize classes =<< unrankOfSize classes size (ClassRank rank)) `shouldBe` Just (size, ClassRank rank)

-- | The sequences of a length that are a trace of the first machine followed by a trace of the second, by brute force.
concatenated :: (Ord step) => StateMachine left step -> StateMachine right step -> Int -> [[step]]
concatenated before after length_ =
    [ steps
    | steps <- replicateM length_ $ nubOrd $ machineSteps before <> machineSteps after
    , or [runs before (take split steps) && runs after (drop split steps) | split <- [0 .. length_]]
    ]

{- | Whether some trace of a state machine has the image, by a search over
pairs of a state and the number of image steps read. A hidden step reads no
image step.
-}
hasImage :: (Ord state, Eq coarse) => StateMachine state step -> (step -> Maybe coarse) -> [coarse] -> Bool
hasImage StateMachine{machineInitial, machineSteps, machineNext, machineFinal} image target =
    search Set.empty [(machineInitial, 0)]
  where
    search _ [] = False
    search seen (pair@(state, position) : pending)
        | Set.member pair seen = search seen pending
        | position == length target && machineFinal state = True
        | otherwise = search (Set.insert pair seen) (next <> pending)
      where
        next =
            [ (after, moved)
            | step <- machineSteps
            , Just after <- [machineNext state step]
            , Just moved <- [advance step]
            ]
        advance step = case image step of
            Nothing -> Just position
            Just coarse
                | take 1 (drop position target) == [coarse] -> Just (position + 1)
                | otherwise -> Nothing

{- | Whether each state has at most one transition for each symbol. Then each
term has at most one run, and 'sized' uses its count table.
-}
deterministic :: (Ord state, Ord symbol) => FTA.FTA state symbol annotation -> Bool
deterministic automaton =
    and
        [ length symbols == length (nubOrd symbols)
        | state <- FTA.states automaton
        , let symbols = map FTA.transitionSymbol $ FTA.transitionsFrom automaton state
        ]

{- | Check that an automaton is deterministic, and that the count table of
'sized' and the route of 'sizedReference' give the same classes in the same
order, up to a length.
-}
checkRoutes :: (Ord state, Ord step, Show step) => FTA.PlainFTA state (TraceSymbol step) -> Int -> Expectation
checkRoutes automaton maximumLength = do
    deterministic automaton `shouldBe` True
    let reference = either (error . show) id $ sizedReference automaton
    forM_ [0 .. maximumLength] $ \length_ ->
        termsOfSize (classesOf automaton) (sizeOf length_) `shouldBe` termsOfSize reference (sizeOf length_)

-- | Check 'feasibility' on a sequence against a run of the state machine.
checkFeasibility :: (Ord state, Show state, Ord step, Show step) => StateMachine state step -> [step] -> Expectation
checkFeasibility machine@StateMachine{machineInitial, machineNext, machineFinal} steps =
    case feasibility (traceAutomaton machine) steps of
        Right states -> do
            runs machine steps `shouldBe` True
            Just states `shouldBe` (pure <$> foldM machineNext machineInitial steps)
        Left (Infeasible done symbol states) -> do
            runs machine steps `shouldBe` False
            -- The steps before the failure run, and the next symbol fails in the state after them.
            let after = foldM machineNext machineInitial done
            take (length done) steps `shouldBe` done
            (pure <$> after) `shouldBe` Just states
            case symbol of
                Step step -> do
                    take 1 (drop (length done) steps) `shouldBe` [step]
                    ((`machineNext` step) <$> after) `shouldBe` Just Nothing
                End -> do
                    length done `shouldBe` length steps
                    (machineFinal <$> after) `shouldBe` Just False

spec :: Spec
spec = describe "Data.CFTA.Trace" $ do
    it "lists, counts, and ranks the traces of each length as brute force does" $
        forM_ [0 .. 7] $ \length_ -> do
            checkLength (stack 3) length_
            checkLength handle length_
            checkLength handle{machineInitial = Opened} length_
            checkLength handle{machineFinal = (== Closed)} length_
    it "samples and shrinks only traces whose preconditions hold" $ do
        let generator = Gen.upToSize (sizeOf 6) $ Gen.fromAutomaton $ fromFTA $ traceAutomaton $ stack 3
            total = either (error . show) id $ Gen.cardinality generator
        total `shouldBe` Cardinality (fromIntegral $ sum [length $ bruteForce (stack 3) length_ | length_ <- [0 .. 6]])
        forM_ (everyRank total) $ \rank ->
            forM_ (rank : Gen.shrinkRank generator rank) $ \candidate ->
                (fmap (runs $ stack 3) . traceSteps <$> Gen.unrank generator candidate) `shouldBe` Right (Just True)
    it "counts the typed stack traces of the trace benchmark language" $ do
        let classes = classesOf $ traceAutomaton typedStack
        forM_ [0 .. 8] $ \length_ ->
            countOfSize classes (sizeOf length_) `shouldBe` Cardinality (Typed.traceCount length_ $ Typed.StackState [])
    it "gives the shortest prefix that has no run and the state in which its last symbol fails" $ do
        feasibility (traceAutomaton handle) [Open, Read, Close] `shouldBe` Right [Closed]
        feasibility (traceAutomaton handle) [Open, Read, Close, Read, Open]
            `shouldBe` Left (Infeasible [Open, Read, Close] (Step Read) [Closed])
        feasibility (traceAutomaton $ stack 3) [Push, Push, Add, Add, Pop]
            `shouldBe` Left (Infeasible [Push, Push, Add] (Step Add) [1])
        feasibility (traceAutomaton handle{machineFinal = (== Closed)}) [Open, Read]
            `shouldBe` Left (Infeasible [Open, Read] End [Opened])
        forM_ [0 .. 5] $ \length_ -> do
            mapM_ (checkFeasibility $ stack 2) $ replicateM length_ [minBound .. maxBound]
            mapM_ (checkFeasibility handle{machineFinal = (== Closed)}) $ replicateM length_ [Open, Read, Close]
    it "intersects two state machines over one step type" $ do
        let both = intersection (traceAutomaton handle) (traceAutomaton atMostTwoReads)
        forM_ [0 .. 7] $ \length_ ->
            fmap sort (tracesOf both length_) `shouldBe` Just (sort $ filter (runs atMostTwoReads) $ bruteForce handle length_)
        -- The state in which the step fails tells which state machine rejects it.
        feasibility both [Open, Read, Read, Close, Open, Read]
            `shouldBe` Left (Infeasible [Open, Read, Read, Close, Open] (Step Read) [FTA.ProductState Opened 2])
    it "finds the shortest trace that reads and ends closed" $ do
        let reads_ = StateMachine False [Open, Read, Close] (\seen step -> Just $ seen || step == Read) id
            both = intersection (traceAutomaton handle{machineFinal = (== Closed)}) (traceAutomaton reads_)
        (fmap traceSteps <$> Gen.smallest (Gen.fromAutomaton $ fromFTA both)) `shouldBe` Right (Just $ Just [Open, Read, Close])
    it "excludes the shortest failing prefixes from every sequence and gives the traces" $ do
        -- The dead prefixes of a search with an external check: here the check is the state machine.
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
    it "unrolls a state machine with an unbounded state to a length bound" $ do
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
            image = FTA.mapSymbols (fmap coarse) fineTraces
        forM_ [0 .. 6] $ \length_ -> do
            fmap sort (tracesOf fineTraces length_)
                `shouldBe` Just (sort [steps | steps <- replicateM length_ fine, runs handle (map coarse steps)])
            fmap sort (tracesOf image length_) `shouldBe` Just (sort $ bruteForce handle length_)
    it "determinizes with one state for each reached set of states, up to 2^n - 1" $
        forM_ [1 .. 5] $ \place -> do
            let result = determinize $ pushFromEnd place
            length (FTA.states result) `shouldBe` 2 ^ place
            checkRoutes result 8
            forM_ [0 .. 8] $ \length_ ->
                fmap sort (tracesOf result length_)
                    `shouldBe` Just
                        ( sort
                            [ steps
                            | steps <- replicateM length_ [Push, Pop]
                            , length_ >= place
                            , take 1 (drop (length_ - place) steps) == [Push]
                            ]
                        )
    it "concatenates two trace languages with one run for each trace" $ do
        let sessions = handle{machineFinal = (== Closed)}
            result = concatenate (traceAutomaton atMostTwoReads) (traceAutomaton sessions)
        checkRoutes result 7
        forM_ [0 .. 7] $ \length_ ->
            fmap sort (tracesOf result length_) `shouldBe` Just (sort $ concatenated atMostTwoReads sessions length_)
        -- The generators accept the result, and they count the same traces.
        Gen.cardinality (Gen.upToSize (sizeOf 7) $ Gen.fromAutomaton $ fromFTA result)
            `shouldBe` Right (Cardinality $ fromIntegral $ sum [length $ concatenated atMostTwoReads sessions length_ | length_ <- [0 .. 7]])
        -- A sequence of reads splits in one more way than its length, and it is one trace.
        let reads_ = concatenate (traceAutomaton $ free [Read]) (traceAutomaton $ free [Read])
        checkRoutes reads_ 7
        forM_ [0 .. 7] $ \length_ -> tracesOf reads_ length_ `shouldBe` Just [replicate length_ Read]
        -- The count table counts the 2^40 traces of 40 steps without a list of them.
        let words_ = classesOf $ concatenate (traceAutomaton $ free [Open, Read]) (traceAutomaton $ free [Open, Read])
        timeout 10000000 (evaluate $ countOfSize words_ $ sizeOf 40) `shouldReturn` Just (2 ^ (40 :: Int))
    it "projects to a coarser step alphabet with one run for each trace" $ do
        let typed = traceAutomaton typedStack
            image = FTA.mapSymbols (fmap shape) typed
            reference = either (error . show) id $ sizedReference image
            result = project shape typed
        -- Two pushes of one shape go to different stacks, so the image has two runs of a trace.
        deterministic image `shouldBe` False
        checkRoutes result 6
        forM_ [0 .. 5] $ \length_ -> do
            fmap sort (tracesOf result length_)
                `shouldBe` Just (sort $ nubOrd $ map (map shape) $ bruteForce typedStack length_)
            countOfSize (classesOf result) (sizeOf length_) `shouldBe` countOfSize reference (sizeOf length_)
    it "hides steps in a projection, also on a cycle of hidden steps" $ do
        let hidePops command = if command == Typed.Pop then Nothing else Just $ shape command
            withoutPops = projectMaybe hidePops $ traceAutomaton typedStack
        checkRoutes withoutPops 6
        forM_ [0 .. 5] $ \length_ ->
            fmap sort (tracesOf withoutPops length_)
                `shouldBe` Just
                    (sort [steps | steps <- replicateM length_ [Pushes, Combines, Negates], hasImage typedStack hidePops steps])
        -- Open and Close form a cycle of hidden steps between the reads.
        let onlyReads step = if step == Read then Just Read else Nothing
            reads_ = projectMaybe onlyReads $ traceAutomaton handle{machineFinal = (== Closed)}
            nothing = projectMaybe (const Nothing :: HandleStep -> Maybe HandleStep) $ traceAutomaton handle
        checkRoutes reads_ 7
        forM_ [0 .. 7] $ \length_ -> do
            tracesOf reads_ length_ `shouldBe` Just [replicate length_ Read]
            tracesOf nothing length_ `shouldBe` Just [[] | length_ == 0]
