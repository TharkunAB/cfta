module Data.CFTA.Gen.Refinement.TraceSpec (spec) where

import Control.Monad (forM_, replicateM)
import Data.Either (isRight)
import Data.List (sort)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.Trace
import Data.CFTA.Index (Cardinality (..), Rank (..), Size (..))
import Data.CFTA.Refinement (Entailment)
import Data.CFTA.Refinement.Expression (literal)
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Refinement.Symbolic (Symbolic (..), true)
import Data.CFTA.Sized (Sized, countOfSize, sized)
import Data.CFTA.Trace (Infeasible (..), StateMachine (..), TraceSymbol (Step), traceAutomaton)

-- | A bank account: deposit or withdraw an amount in the range. A withdrawal needs the balance.
account :: Integer -> GuardedMachine
account maximumAmount =
    GuardedMachine
        [("balance", 0)]
        [ GuardedStep
            "deposit"
            (Just (1, maximumAmount))
            (\_ _ -> true)
            (\state amount -> [("balance", state "balance" + amount)])
        , GuardedStep
            "withdraw"
            (Just (1, maximumAmount))
            (\state amount -> amount .<= state "balance")
            (\state amount -> [("balance", state "balance" - amount)])
        ]

-- | A counter from zero to the bound, with steps without a parameter.
counter :: Integer -> GuardedMachine
counter bound =
    GuardedMachine
        [("count", 0)]
        [ GuardedStep
            "increment"
            Nothing
            (\state _ -> state "count" .< literal bound)
            (\state _ -> [("count", state "count" + 1)])
        , GuardedStep "decrement" Nothing (\state _ -> state "count" .> 0) (\state _ -> [("count", state "count" - 1)])
        ]

-- | At most two withdrawals of an amount up to a million. The state counts them.
twoWithdrawals :: GuardedMachine
twoWithdrawals =
    GuardedMachine
        [("withdrawals", 0)]
        [ GuardedStep "deposit" (Just (1, 1000000)) (\_ _ -> true) (\_ _ -> [])
        , GuardedStep
            "withdraw"
            (Just (1, 1000000))
            (\state _ -> state "withdrawals" .< 2)
            (\state _ -> [("withdrawals", state "withdrawals" + 1)])
        ]

-- | The account with amounts 1 and 2, and a step without a parameter that keeps the balance.
audited :: GuardedMachine
audited = (account 2){guardedSteps = guardedSteps (account 2) <> [GuardedStep "audit" Nothing (\_ _ -> true) (\_ _ -> [])]}

-- | The events of a machine: each step with each value of its range.
alphabet :: GuardedMachine -> [Event]
alphabet = machineSteps . unrolled 0

-- | The sequences of at most the bound of events that the run accepts, by brute force.
bruteForce :: Int -> GuardedMachine -> [[Event]]
bruteForce bound machine =
    [ events
    | length_ <- [0 .. bound]
    , events <- replicateM length_ (alphabet machine)
    , isRight $ guardedRun machine events
    ]

-- | The size classes of the unrolled automaton.
unrolledClasses :: Int -> GuardedMachine -> Sized (TraceSymbol Event)
unrolledClasses bound = either (error . show) id . sized . traceAutomaton . unrolled bound

-- | The traces of exactly the given number of steps on the unrolled route.
unrolledCountOfLength :: Int -> GuardedMachine -> Int -> Cardinality
unrolledCountOfLength bound machine length_ = countOfSize (unrolledClasses bound machine) (Size $ fromIntegral length_ + 1)

-- | The traces of at most the bound of steps on the unrolled route.
unrolledCount :: Int -> GuardedMachine -> Cardinality
unrolledCount bound machine = sum $ map (unrolledCountOfLength bound machine) [0 .. bound]

-- | Compile a generator with a solver.
compiled :: Entailment -> LTAGen.LTAGen a -> IO (LTAGen.LTAGen a)
compiled solver generator = either (error . show) id <$> LTAGen.compileWith solver generator

-- | The cardinality of a compiled generator.
cardinalityOf :: LTAGen.LTAGen a -> Cardinality
cardinalityOf = either (error . show) id . LTAGen.cardinality

-- | Two steps of the account.
deposit, withdraw :: Integer -> Event
deposit = Event "deposit" . Just
withdraw = Event "withdraw" . Just

spec :: Spec
spec = describe "Data.CFTA.Gen.Refinement.Trace" $ do
    it "counts and lists the traces of the account as the unrolled automaton and brute force do" $
        withZ3 [] $ \solver -> do
            forM_ [0 .. 5] $ \bound -> do
                generator <- compiled solver $ guardedTraces bound (account 2)
                cardinalityOf generator `shouldBe` unrolledCount bound (account 2)
                fmap sort (LTAGen.values generator) `shouldBe` Right (sort $ bruteForce bound (account 2))
            forM_ [0 .. 4] $ \bound -> do
                generator <- compiled solver $ guardedTraces bound (account 7)
                cardinalityOf generator `shouldBe` unrolledCount bound (account 7)
    it "counts the bounded counter as the unrolled automaton does" $
        withZ3 [] $ \solver ->
            forM_ [0 .. 6] $ \bound -> do
                generator <- compiled solver $ guardedTraces bound (counter 3)
                cardinalityOf generator `shouldBe` unrolledCount bound (counter 3)
    it "counts amounts up to a million without a list of them, and decodes and shrinks traces that run" $
        withZ3 [] $ \solver -> do
            let n = 1000000
                machine = account n
            oneStep <- compiled solver $ guardedTraces 1 machine
            cardinalityOf oneStep `shouldBe` Cardinality (1 + n)
            twoSteps <- compiled solver $ guardedTraces 2 machine
            cardinalityOf twoSteps `shouldBe` Cardinality (1 + n + n * n + n * (n + 1) `div` 2)
            threeSteps <- compiled solver $ guardedTraces 3 machine
            let Cardinality total = cardinalityOf threeSteps
            forM_ [0, 1, total `div` 3, total `div` 2, total - 1] $ \rank -> do
                fmap (guardedRun machine) (LTAGen.unrank threeSteps (Rank rank)) `shouldSatisfy` either (const False) isRight
                forM_ (take 20 $ LTAGen.shrinkRank threeSteps (Rank rank)) $ \smaller ->
                    fmap (guardedRun machine) (LTAGen.unrank threeSteps smaller) `shouldSatisfy` either (const False) isRight
    it "has the traces of n steps at size 2n + 1, also with steps without a parameter" $
        withZ3 [] $ \solver -> do
            generator <- compiled solver $ guardedTraces 5 audited
            forM_ [0 .. 5] $ \length_ -> do
                LTAGen.countAtSize generator (Size $ 2 * fromIntegral length_ + 1)
                    `shouldBe` Right (unrolledCountOfLength 5 audited length_)
                LTAGen.countAtSize generator (Size $ 2 * fromIntegral length_ + 2) `shouldBe` Right 0
    it "counts the product of the account and at most two withdrawals" $
        withZ3 [] $ \solver -> do
            let both = guardedProduct (account 2) twoWithdrawals
            forM_ [0 .. 5] $ \bound -> do
                generator <- compiled solver $ guardedTraces bound both
                cardinalityOf generator `shouldBe` unrolledCount bound both
                fmap sort (LTAGen.values generator)
                    `shouldBe` Right (sort [events | events <- bruteForce bound (account 2), isRight $ guardedRun twoWithdrawals events])
            -- With a million, a third withdrawal first fits in four steps.
            let large = guardedProduct (account 1000000) twoWithdrawals
            forM_ [(3, (==)), (4, (<))] $ \(bound, compare_) -> do
                product_ <- compiled solver $ guardedTraces bound large
                alone <- compiled solver $ guardedTraces bound (account 1000000)
                cardinalityOf product_ `shouldSatisfy` (`compare_` cardinalityOf alone)
    it "intersects the parameter ranges of a step that both machines have" $
        withZ3 [] $ \solver -> do
            let step name range = GuardedStep name range (\_ _ -> true) (\_ _ -> [])
                first =
                    GuardedMachine [] [step "deposit" (Just (1, 5)), step "fee" (Just (1, 2)), step "audit" Nothing, step "close" Nothing]
                second =
                    GuardedMachine
                        []
                        [step "deposit" (Just (3, 10)), step "fee" (Just (5, 6)), step "audit" (Just (0, 1)), step "close" Nothing]
                both = guardedProduct first second
            map (\kind -> (stepName kind, stepRange kind)) (guardedSteps both)
                `shouldBe` [("deposit", Just (3, 5)), ("close", Nothing)]
            forM_ [0 .. 3] $ \bound -> do
                generator <- compiled solver $ guardedTraces bound both
                fmap sort (LTAGen.values generator)
                    `shouldBe` Right (sort [events | events <- bruteForce bound first, isRight $ guardedRun second events])
    it "runs a sequence and gives the shortest prefix that fails and the state before it" $ do
        let machine = account 5
            balance value = [("balance", value)]
        guardedRun machine [deposit 5, withdraw 3, withdraw 2] `shouldBe` Right (balance 0)
        guardedRun machine [deposit 5, withdraw 3, withdraw 3, deposit 1]
            `shouldBe` Left (Infeasible [deposit 5, withdraw 3] (Step $ withdraw 3) [balance 2])
        guardedRun machine [deposit 2, deposit 6] `shouldBe` Left (Infeasible [deposit 2] (Step $ deposit 6) [balance 2])
        guardedRun machine [Event "deposit" Nothing]
            `shouldBe` Left (Infeasible [] (Step $ Event "deposit" Nothing) [balance 0])
        guardedRun machine [Event "close" Nothing] `shouldBe` Left (Infeasible [] (Step $ Event "close" Nothing) [balance 0])
        -- The state of the product has the names of both machines.
        guardedRun (guardedProduct machine twoWithdrawals) [deposit 5, withdraw 1, withdraw 1, withdraw 1]
            `shouldBe` Left (Infeasible [deposit 5, withdraw 1, withdraw 1] (Step $ withdraw 1) [[("balance", 3), ("withdrawals", 2)]])
    it "compiles the account with the lattice entailment and no solver process" $ do
        let n = 1000000
        twoSteps <- compiled latticeEntailment $ guardedTraces 2 (account n)
        cardinalityOf twoSteps `shouldBe` Cardinality (1 + n + n * n + n * (n + 1) `div` 2)
