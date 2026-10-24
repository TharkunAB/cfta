module Data.CFTA.Sized.PrefixGuardSpec (spec) where

import Control.Monad (forM, forM_, when, zipWithM)
import Data.Containers.ListUtils (nubOrd)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (genericLength, inits, isPrefixOf, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint,
    Guard (..),
    conjoinConstraints,
    equalities,
    equalityConstraint,
    noConstraint,
    semanticConstraint,
 )
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Index (Cardinality (..), Size (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Refinement.Denotation (accepts)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Expression (Formula, refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.Verdict (Entailment (Entailment), Verdict (..), andVerdicts, orVerdicts)
import Data.CFTA.Sized (SizedError (..), sized, sizedUpTo, termsOfSize)
import Data.CFTA.Sized.Prefix
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Sized.Prefix with a solver" $ do
    forM_ guardFixtures $ \(name, bound, graph) -> describe name $ do
        it "offers, leaves undecided, and rejects each token as a search of the runs of every term does" $
            agreesWithSearch bound graph
        it "accepts the terms that the reference denotation accepts, and rejects the terms that it rejects" $
            agreesWithDenotation bound graph
    it "offers, leaves undecided, and rejects one token each after a pair node" $ do
        completions <- prefixCompletionsWith partialEntailment 3 guardedPairs
        let after = afterToken completions (sym "g", 2)
        fmap nextTokens after `shouldBe` Just [((number 2, 0), 3)]
        fmap undecidedTokens after `shouldBe` Just [((number 3, 0), 3)]
        fmap (isJust . (`afterToken` (number 1, 0))) after `shouldBe` Just False
    it "offers a token that also has undecided completions" $ do
        completions <- prefixCompletionsWith partialEntailment 7 guardedLists
        let after = afterPrefix completions [(sym "g", 2), (number 2, 0)]
        fmap completionCount after `shouldBe` Just 6
        fmap (length . undecidedTerms) after `shouldBe` Just 8
    it "says that a complete prefix that the solver does not decide is undecided" $ do
        completions <- prefixCompletionsWith partialEntailment 3 guardedPairs
        let after = afterPrefix completions [(sym "g", 2), (number 3, 0), (number 1, 0)]
        fmap completeVerdict after `shouldBe` Just Unknown
        fmap isComplete after `shouldBe` Just False
    it "rejects a term with a failed guard, where the reference denotation is undecided" $ do
        -- In g(1, g(3, 1)), the outer guard fails on 1, and the inner guard is
        -- undecided on 3. The reference does not decide the outer guard.
        let leaf value = Term.Node (number value) []
            term = Term.Node (sym "g") [leaf 1, Term.Node (sym "g") [leaf 3, leaf 1]]
        reference <- accepts partialEntailment (fromFTA guardedLists) term
        completions <- prefixCompletionsWith partialEntailment 5 guardedLists
        (reference, term `elem` (completionTerms completions <> undecidedTerms completions)) `shouldBe` (Unknown, False)
    it "accepts the terms of sizedUpTo where the solver decides every guard" $ do
        completions <- prefixCompletionsWith partialEntailment 7 decidedLists
        classes <- sizedUpTo partialEntailment 7 decidedLists >>= either (fail . show) pure
        let expected = concat [termsOfSize classes (Size size) | size <- [1 .. 7]]
        sort (completionTerms completions) `shouldBe` sort expected
        undecidedTerms completions `shouldBe` []
        forM_ (nubOrd $ concatMap (inits . preorder) expected) $ \prefix ->
            (prefix, sort . completionTerms <$> afterPrefix completions prefix)
                `shouldBe` (prefix, Just $ sort $ filter ((prefix `isPrefixOf`) . preorder) expected)
    it "accepts the terms of sizedUpTo below the first size where it stops at an undecided guard" $ do
        stopped <- sizedUpTo partialEntailment 7 guardedLists
        below <- case stopped of
            Left (GuardUnknown _ term) -> pure $ toInteger (length term) - 1
            other -> fail $ "expected an undecided guard, not " <> either show (const "classes") other
        classes <- sizedUpTo partialEntailment (Size below) guardedLists >>= either (fail . show) pure
        completions <- prefixCompletionsWith partialEntailment (Size below) guardedLists
        sort (completionTerms completions) `shouldBe` sort (concat [termsOfSize classes (Size size) | size <- [1 .. below]])
        undecidedTerms completions `shouldBe` []
    it "does not call the solver without a guard" $ do
        forM_ [("pairs", pairsWith noConstraint), ("equal pairs", pairsWith equalChildren)] $ \(name, graph) -> do
            completions <- prefixCompletionsWith unusedEntailment 3 graph
            let expected = either (error . show) id $ prefixCompletions 3 graph
            (name, completionTerms completions, nextTokens completions)
                `shouldBe` (name, completionTerms expected, nextTokens expected)
    it "asks the solver less often than a search of the same candidates without a memory" $ do
        (counted, calls) <- countingEntailment partialEntailment
        _ <- completionTerms <$> prefixCompletionsWith counted 7 guardedLists
        made <- readIORef calls
        -- The candidates: the terms of the automaton with only its equality constraints.
        let reduced = either (error . show) id $ sized $ FTA.mapConstraints (equalityConstraint . equalities) guardedLists
            terms = concat [termsOfSize reduced (Size size) | size <- [1 .. 7]]
        (searched, searchCalls) <- countingEntailment partialEntailment
        forM_ terms (searchVerdict searched guardedLists)
        searchMade <- readIORef searchCalls
        (made, searchMade) `shouldSatisfy` uncurry (<)
    it "rejects a constrained automaton without a solver" $
        either Just (const Nothing) (prefixCompletions 3 guardedPairs) `shouldBe` Just GuardedTransition

{- | The completions and the undecided completions of each prefix, against a
search of every term over the symbols of the automaton: a term is accepted
when some run has every guard 'Yes', rejected when each run has a 'No' guard,
and undecided otherwise.
-}
agreesWithSearch :: Integer -> FTA.FTA String Symbol Constraint -> IO ()
agreesWithSearch bound graph = do
    completions <- prefixCompletionsWith partialEntailment (Size bound) graph
    let terms = candidates bound graph
    verdicts <- forM terms (searchVerdict partialEntailment graph)
    let decided = zip (map preorder terms) verdicts
        with verdict prefix = [tokens | (tokens, found) <- decided, found == verdict, prefix `isPrefixOf` tokens]
        counts verdict prefix =
            Map.fromListWith
                (+)
                [(tokens !! length prefix, 1 :: Integer) | tokens <- with verdict prefix, length tokens > length prefix]
        verdictOf prefix = fromMaybe No $ lookup prefix [(tokens, found) | (tokens, found) <- decided, found /= No]
    forM_ (nubOrd $ concatMap (inits . fst) decided) $ \prefix -> do
        let accepted = counts Yes prefix
            undecided = counts Unknown prefix
            live = not (null $ with Yes prefix) || not (null $ with Unknown prefix)
        case afterPrefix completions prefix of
            Nothing -> (prefix, live) `shouldBe` (prefix, False)
            Just after -> do
                (prefix, nextTokens after)
                    `shouldBe` (prefix, [(token, Cardinality count) | (token, count) <- Map.toList accepted])
                (prefix, undecidedTokens after)
                    `shouldBe` ( prefix
                               , [ (token, Cardinality count)
                                 | (token, count) <- Map.toList undecided
                                 , Map.notMember token accepted
                                 ]
                               )
                (prefix, completeVerdict after) `shouldBe` (prefix, verdictOf prefix)
                (prefix, completionCount after, genericLength $ undecidedTerms after)
                    `shouldBe` (prefix, genericLength $ with Yes prefix, genericLength (with Unknown prefix) :: Integer)
                (prefix, sort $ map preorder $ completionTerms after) `shouldBe` (prefix, sort $ with Yes prefix)
                (prefix, sort $ map preorder $ undecidedTerms after) `shouldBe` (prefix, sort $ with Unknown prefix)
                -- A rejected token has no accepted and no undecided completion.
                ( prefix
                    , [ token
                      | token <- alphabet graph
                      , Map.notMember token accepted
                      , Map.notMember token undecided
                      , isJust $ afterToken after token
                      ]
                    )
                    `shouldBe` (prefix, [])

{- | 'Yes' of the reference denotation is 'Yes' here, and its 'No' is 'No' here.
The verdict here can be 'No' where the reference is 'Unknown'.
-}
agreesWithDenotation :: Integer -> FTA.FTA String Symbol Constraint -> IO ()
agreesWithDenotation bound graph = do
    completions <- prefixCompletionsWith partialEntailment (Size bound) graph
    forM_ (candidates bound graph) $ \term -> do
        reference <- accepts partialEntailment (fromFTA graph) term
        let found
                | term `elem` completionTerms completions = Yes
                | term `elem` undecidedTerms completions = Unknown
                | otherwise = No
        (term, reference == Yes) `shouldBe` (term, found == Yes)
        when (reference == No) $ (term, found) `shouldBe` (term, No)

-- | The verdict of a term from the explicit runs of the automaton, without a memory.
searchVerdict :: Entailment -> FTA.FTA String Symbol Constraint -> Term Symbol -> IO Verdict
searchVerdict entailment graph term =
    orVerdicts
        [ andVerdicts [evaluateConstraint entailment constraint subterm | (constraint, subterm) <- run]
        | run <- runs (FTA.initialState graph) term
        ]
  where
    runs state subterm@(Term.Node symbol children) =
        [ (FTA.transitionConstraint transition, subterm) : concat below
        | transition <- FTA.transitionsFrom graph state
        , FTA.transitionSymbol transition == symbol
        , length (FTA.transitionChildren transition) == length children
        , below <- zipWithM runs (FTA.transitionChildren transition) children
        ]

-- | Every term over the tokens of an automaton with at most the given number of nodes.
candidates :: Integer -> FTA.FTA String Symbol Constraint -> [Term Symbol]
candidates bound graph = concatMap exactly [1 .. bound]
  where
    tokens =
        nubOrd
            [ (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
            | transition <- concat $ Map.elems $ FTA.transitionTable graph
            ]
    exactly size = [Term.Node symbol children | (symbol, arity) <- tokens, children <- spread arity (size - 1)]
    spread 0 0 = [[]]
    spread 0 _ = []
    spread arity remaining =
        [ first : rest
        | firstSize <- [1 .. remaining - toInteger (arity - 1)]
        , first <- exactly firstSize
        , rest <- spread (arity - 1) (remaining - firstSize)
        ]

-- | The tokens of an automaton, and each symbol with one more child.
alphabet :: FTA.FTA String Symbol Constraint -> [(Symbol, Int)]
alphabet graph =
    nubOrd $
        concat
            [ [(FTA.transitionSymbol transition, arity), (FTA.transitionSymbol transition, arity + 1)]
            | transition <- concat $ Map.elems $ FTA.transitionTable graph
            , let arity = length $ FTA.transitionChildren transition
            ]

-- | The tokens of a term in preorder.
preorder :: Term symbol -> [(symbol, Int)]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children

-- | The automata with guards, each with a name and a bound.
guardFixtures :: [(String, Integer, FTA.FTA String Symbol Constraint)]
guardFixtures =
    [ ("pairs whose first child is above one", 3, guardedPairs)
    ,
        ( "pairs whose two children are above one"
        , 3
        , pairsWith $ semanticConstraint $ And [Satisfies (ECTA.path [0]) aboveOne, Satisfies (ECTA.path [1]) aboveOne]
        )
    , ("equal pairs whose first child is above one", 3, pairsWith $ conjoinConstraints equalChildren firstAboveOne)
    , ("lists whose numbers are above one", 7, guardedLists)
    , ("lists of 1 and 2 whose numbers are above one", 7, decidedLists)
    ]

-- | The pairs g(x, y) of the numbers 1, 2, and 3, whose first child is above one.
guardedPairs :: FTA.FTA String Symbol Constraint
guardedPairs = pairsWith firstAboveOne

-- | The pairs g(x, y) of the numbers 1, 2, and 3, with a constraint on g.
pairsWith :: Constraint -> FTA.FTA String Symbol Constraint
pairsWith constraint = automaton "s" [("s", [FTA.Transition (sym "g") ["q", "q"] constraint]), ("q", map numberLeaf [1, 2, 3])]

{- | The lists g(x, g(y, ... n)) of the numbers 1, 2, and 3 that end in 1 or 2,
with each listed number above one.
-}
guardedLists :: FTA.FTA String Symbol Constraint
guardedLists = listsOf [1, 2, 3]

-- | The lists of 'guardedLists' with the numbers 1 and 2 only, which the solver decides.
decidedLists :: FTA.FTA String Symbol Constraint
decidedLists = listsOf [1, 2]

-- | The lists of the given numbers, with each listed number above one.
listsOf :: [Integer] -> FTA.FTA String Symbol Constraint
listsOf numbers =
    automaton
        "s"
        [ ("s", [numberLeaf 1, numberLeaf 2, FTA.Transition (sym "g") ["q", "s"] firstAboveOne])
        , ("q", map numberLeaf numbers)
        ]

-- | The guard that the first child is above one.
firstAboveOne :: Constraint
firstAboveOne = semanticConstraint $ Satisfies (ECTA.path [0]) aboveOne

-- | The equality of the two children.
equalChildren :: Constraint
equalChildren = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]

-- | A leaf with the refinement that its value is the number.
numberLeaf :: Integer -> FTA.Transition String Symbol Constraint
numberLeaf value = FTA.Transition (number value) [] noConstraint

-- | The symbol n with the refinement that its value is the number.
number :: Integer -> Symbol
number value = RefinedSymbol (sym "n") (valueIs value)

-- | The refinement that the value is the number.
valueIs :: Integer -> Formula
valueIs value = refinementFormula (.== fromInteger value)

-- | The refinement that the value is above one.
aboveOne :: Formula
aboveOne = refinementFormula (.> 1)

{- | A solver that decides only whether the values 1 and 2 are above one, as in
the inclusion tests. It does not decide the value 3, or any other question.
-}
partialEntailment :: Entailment
partialEntailment = Entailment $ \antecedent consequent ->
    pure $
        if consequent /= aboveOne
            then Unknown
            else
                if antecedent == valueIs 2
                    then Yes
                    else if antecedent == valueIs 1 then No else Unknown

-- | A solver and the number of the questions that it answers.
countingEntailment :: Entailment -> IO (Entailment, IORef Int)
countingEntailment (Entailment decide) = do
    calls <- newIORef 0
    pure (Entailment $ \antecedent consequent -> modifyIORef' calls (+ 1) >> decide antecedent consequent, calls)

-- | A solver that fails the test when the queries call it.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> fail "unexpected solver call"

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> FTA.FTA String Symbol Constraint
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A symbol from its name.
sym :: String -> Symbol
sym = Symbol . Text.pack
