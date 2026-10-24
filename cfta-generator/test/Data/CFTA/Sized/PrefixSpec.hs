module Data.CFTA.Sized.PrefixSpec (spec) where

import Control.Monad (forM_)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Functor (void)
import Data.List (genericLength, inits, isPrefixOf, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Gen.Internal.Table (unambiguousRows)
import Data.CFTA.Gen.TypedArithmeticLanguage (arithAutomaton)
import Data.CFTA.Gen.UntypedExpressionLanguage (expressionAutomaton)
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size (..))
import Data.CFTA.Sized (countOfSize, sized, sizedStates, termsOfSize, unrankOfSize)
import Data.CFTA.Sized.Prefix
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec = describe "Data.CFTA.Sized.Prefix" $ do
    it "has unambiguous and ambiguous fixtures" $
        [unambiguous expressionAutomaton, unambiguous overlapping, unambiguous (arithAutomaton 2)]
            `shouldBe` [True, False, True]
    it "counts the terms of the fixtures up to the bound" $
        [ completionCount $ start sizeBound expressionAutomaton
        , completionCount $ start sizeBound overlapping
        , completionCount $ start sizeBound (arithAutomaton 2)
        ]
            `shouldBe` [74, 50, 32]
    it "counts a term with two runs once" $
        -- Each term f(..(a)) has a run through p and a run through q, so a sum
        -- over the stacks gives 15.
        fmap completionCount (afterToken (start sizeBound overlapping) (sym "f", 1)) `shouldBe` Just 10
    fixture "untyped expressions" expressionAutomaton
    fixture "overlapping alternatives" overlapping
    fixture "typed arithmetic" (arithAutomaton 2)
    it "rejects a constrained automaton" $ do
        let equal = equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]
            constrained = automaton "s" [("s", [FTA.Transition (sym "g") ["q", "q"] equal]), ("q", [leaf "a", leaf "b"])]
        either Just (const Nothing) (prefixCompletions 6 constrained) `shouldBe` Just ConstrainedTransition
    it "has no completion below size one" $ do
        let completions = start 0 expressionAutomaton
        completionCount completions `shouldBe` 0
        map fst (nextTokens completions) `shouldBe` []
        isComplete completions `shouldBe` False
        isJust (sampleCompletion completions) `shouldBe` False

{- | The checks of the completions of an automaton up to 'sizeBound', each
against the accepted terms that 'termsOfSize' lists.
-}
fixture ::
    forall state symbol. (Ord state, Ord symbol, Show symbol) => String -> FTA.FTA state symbol Constraint -> Spec
fixture name graph = describe name $ do
    it "lists the size classes in order for the empty prefix" $
        completionTerms empty `shouldBe` accepted
    it "offers each next token with the number of accepted terms that start with the prefix and the token" $
        forM_ prefixes $ \prefix ->
            (prefix, nextTokens <$> afterPrefix empty prefix)
                `shouldBe` ( prefix
                           , Just
                                $ Map.toList
                                $ Map.fromListWith
                                    (+)
                                    [(tokens !! length prefix, 1) | tokens <- preorders, prefix `isPrefixOf` tokens, length tokens > length prefix]
                           )
    it "rejects each other token, and no accepted term starts with the prefix and the token" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                offered = map fst $ nextTokens completions
            ( prefix
                , [(token, isJust $ afterToken completions token, brute $ prefix <> [token]) | token <- alphabet, token `notElem` offered]
                )
                `shouldBe` (prefix, [(token, False, 0) | token <- alphabet, token `notElem` offered])
    it "counts the completions as the offered counts, and one more for a complete prefix" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                complete = if isComplete completions then 1 else 0
            (prefix, completionCount completions, sum (map snd $ nextTokens completions) + complete)
                `shouldBe` (prefix, Cardinality $ brute prefix, Cardinality $ brute prefix)
    it "is complete exactly when the prefix is an accepted term" $
        forM_ prefixes $ \prefix ->
            (prefix, isComplete $ after prefix) `shouldBe` (prefix, prefix `elem` preorders)
    it "lists and unranks each completion once, accepted and with the prefix" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                listed = completionTerms completions
                count = genericLength listed
            (prefix, sort listed) `shouldBe` (prefix, sort [term | term <- accepted, prefix `isPrefixOf` preorder term])
            (prefix, completionCount completions) `shouldBe` (prefix, Cardinality count)
            (prefix, map (unrankCompletion completions . Rank) [-1 .. count])
                `shouldBe` (prefix, [Nothing] <> map Just listed <> [Nothing])
            (prefix, filter (\term -> not (FTA.accepts plain term && prefix `isPrefixOf` preorder term)) listed)
                `shouldBe` (prefix, [])
    it "samples completions with the prefix, the same for the same seed" $
        forM_ prefixes $ \prefix -> do
            let completions = after prefix
                draw gen = QCGen.unGen (QC.vectorOf 20 gen) (QCRandom.mkQCGen 20261023) 30
            case sampleCompletion completions of
                Nothing -> (prefix, completionCount completions) `shouldBe` (prefix, 0)
                Just gen -> do
                    (prefix, draw gen) `shouldBe` (prefix, draw gen)
                    (prefix, filter (`notElem` completionTerms completions) (draw gen)) `shouldBe` (prefix, [])
    it "reads the classes that sized gives with each state as the initial state" $
        forM_ (Map.keys $ FTA.transitionTable $ FTA.trim graph) $ \state -> do
            let shared = either (error . show) id (sizedStates graph) state
                alone =
                    either (error . show) id
                        $ sized
                        $ fromRight (error "a state of a valid automaton is a valid initial state")
                        $ FTA.mkFTA state (Map.toList $ FTA.transitionTable graph)
            forM_ [1 .. sizeBound] $ \size -> do
                let Cardinality count = countOfSize alone (Size size)
                    classOf found = (termsOfSize found (Size size), [unrankOfSize found (Size size) (ClassRank rank) | rank <- [-1 .. count]])
                (size, countOfSize shared (Size size), classOf shared) `shouldBe` (size, Cardinality count, classOf alone)
    it "rejects invalid prefixes" $
        forM_ invalid $ \prefix -> do
            (prefix, isJust $ afterPrefix empty prefix) `shouldBe` (prefix, False)
            (prefix, brute prefix) `shouldBe` (prefix, 0)
  where
    plain = FTA.dropConstraints graph
    empty = start sizeBound graph
    after prefix = fromMaybe (error $ "no completions after " <> show prefix) $ afterPrefix empty prefix
    classes = either (error . show) id $ sized graph
    accepted = concat [termsOfSize classes (Size size) | size <- [1 .. sizeBound]]
    preorders = map preorder accepted
    prefixes = nubOrd $ concatMap inits preorders
    brute :: [(symbol, Int)] -> Integer
    brute prefix = genericLength $ filter (prefix `isPrefixOf`) preorders
    -- Each token of the automaton, and each symbol with one more child.
    alphabet =
        nubOrd $
            concat
                [ [(FTA.transitionSymbol transition, arity), (FTA.transitionSymbol transition, arity + 1)]
                | transition <- concat $ Map.elems $ FTA.transitionTable graph
                , let arity = length $ FTA.transitionChildren transition
                ]
    -- A wrong token after a prefix, a token after a complete term, and a
    -- term above the bound.
    invalid =
        take 5 [prefix <> [token] | prefix <- prefixes, token <- alphabet, token `notElem` map fst (nextTokens $ after prefix)]
            <> take 3 [tokens <> [token] | tokens <- preorders, token <- alphabet]
            <> take 3 (map preorder $ termsOfSize classes (Size $ sizeBound + 1))

-- | The largest size of the completions.
sizeBound :: Integer
sizeBound = 6

-- | The completions of the empty prefix up to a bound.
start :: (Ord state, Ord symbol) => Integer -> FTA.FTA state symbol Constraint -> Completions symbol
start bound = either (error . show) id . prefixCompletions (Size bound)

-- | Whether the rows of an automaton are unambiguous.
unambiguous :: (Ord state, Eq symbol) => FTA.FTA state symbol Constraint -> Bool
unambiguous = unambiguousRows . Map.map (map void) . FTA.transitionTable

-- | The tokens of a term in preorder.
preorder :: Term symbol -> [(symbol, Int)]
preorder (Term.Node symbol children) = (symbol, length children) : concatMap preorder children

-- | A recursion in which @f(a)@ and @f(f(a))@ have two runs.
overlapping :: FTA.FTA String Symbol Constraint
overlapping =
    automaton
        "s"
        [ ("s", [leaf "a", node "f" ["p"], node "f" ["q"], node "g" ["s", "s"]])
        , ("p", [leaf "a", leaf "b", node "f" ["p"]])
        , ("q", [leaf "a", node "f" ["q"]])
        ]

-- | An automaton from rows of named states.
automaton :: String -> [(String, [FTA.Transition String Symbol Constraint])] -> FTA.FTA String Symbol Constraint
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

-- | A transition without children.
leaf :: String -> FTA.Transition String Symbol Constraint
leaf symbol = FTA.Transition (sym symbol) [] noConstraint

-- | A transition without a constraint.
node :: String -> [String] -> FTA.Transition String Symbol Constraint
node symbol children = FTA.Transition (sym symbol) children noConstraint

-- | A symbol from its name.
sym :: String -> Symbol
sym = Symbol . Text.pack
