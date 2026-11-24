{-# LANGUAGE OverloadedStrings #-}

-- | Template lowerings: lowered terms, the inverse image of a spec, and the check of a later grammar.
module Data.CFTA.LoweringSpec (spec) where

import Control.Monad ((>=>))
import Data.List (nub)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import Test.QuickCheck (
    Gen,
    Property,
    checkCoverage,
    choose,
    counterexample,
    cover,
    elements,
    forAll,
    frequency,
    property,
    vectorOf,
 )

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Lowering (Expansion (..), ExpansionError (..), LoweringError (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Path (path)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term (Node))

-- | The states of the specs: the parity of the value of a term.
data Parity = Even | Odd
    deriving (Eq, Ord, Show)

spec :: Spec
spec = describe "template lowerings" $ do
    it "put the lowered children in the expansion" $ do
        Lowering.lower lowering (double one) `shouldBe` Just (add one one)
        Lowering.lower lowering (successor (double zero)) `shouldBe` Just (add (add zero zero) one)
        Lowering.lower lowering (add one zero) `shouldBe` Just (add one zero)

    it "lift a spec to the terms whose lowering it accepts" $ do
        lifted <- either (fail . show) pure $ Lowering.lift lowering evenValue
        let within = FTA.dropConstraints $ FTA.intersect later lifted
            bounded = Set.fromList $ FTA.terms $ FTA.boundDepth 3 later
            expected = Set.filter (maybe False (FTA.accepts evenValue) . Lowering.lower lowering) bounded
        Set.fromList (FTA.terms $ FTA.boundDepth 3 within) `shouldBe` expected
        Set.size expected `shouldSatisfy` (> 10)

    it "lifts an ordinary target into a source grammar when a copied child needs two states" $ do
        let target =
                either (error . show) id $
                    FTA.mkFTA
                        (0 :: Int)
                        [(0, [FTA.Transition "add" [1, 2] ()]), (1, [FTA.Transition "zero" [] ()]), (2, [FTA.Transition "zero" [] ()])]
            both = double zero
        lifted <- either (fail . show) pure $ Lowering.liftFrom lowering (FTA.fromTerms [both, double one]) target
        FTA.terms lifted `shouldBe` [both]

    it "retains well-formed discarded children from the source grammar" $ do
        let projection = either (error . show) id $ Lowering.mkLowering [("fst", 2, Child 0)]
            pair right = Node "fst" [zero, right]
            good = pair (Node "source-only" [one])
            malformed = pair (Node "fst" [])
            target = FTA.mapConstraints (const ()) $ FTA.fromTerms [zero]
        lifted <- either (fail . show) pure $ Lowering.liftFrom projection (FTA.fromTerms [malformed, good]) target
        FTA.terms lifted `shouldBe` [good]

    it "checks retained source equalities even for children the target discards" $ do
        let equalChildren = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
            source =
                either (error . show) id $
                    FTA.mkFTA
                        (0 :: Int)
                        [ (0, [FTA.Transition "keep" [1, 1] equalChildren])
                        , (1, [FTA.Transition "zero" [] noConstraint, FTA.Transition "one" [] noConstraint])
                        ]
            constant = either (error . show) id $ Lowering.mkLowering [("keep", 2, Apply "zero" [])]
            target = FTA.mapConstraints (const ()) $ FTA.fromTerms [zero]
        lifted <- either (fail . show) pure $ Lowering.liftFrom constant source target
        map (FTA.accepts lifted) [Node "keep" [zero, zero], Node "keep" [zero, one]] `shouldBe` [True, False]

    it "compose: lowering with a composite is lowering twice" $ do
        -- quad(x) lowers to double(double(x)), which lowers to sums.
        let upper = either (error . show) id $ Lowering.mkLowering [("quad", 1, Apply "double" [Apply "double" [Child 0]])]
            compose second first = either (error . show) id $ Lowering.compose second first
            composite = compose upper lowering
            terms = FTA.terms $ FTA.boundDepth 3 $ grammar [("double", 1), ("succ", 1), ("quad", 1)]
        length terms `shouldSatisfy` (> 10)
        map (Lowering.lower composite) terms
            `shouldBe` map (Lowering.lower upper >=> Lowering.lower lowering) terms
        map (Lowering.lower (compose Lowering.identity lowering)) terms `shouldBe` map (Lowering.lower lowering) terms
        map (Lowering.lower (compose lowering Lowering.identity)) terms `shouldBe` map (Lowering.lower lowering) terms
        let top = grammar [("double", 1), ("succ", 1), ("quad", 1)]
            within lifted = Set.fromList $ FTA.terms $ FTA.boundDepth 3 $ FTA.dropConstraints $ FTA.intersect top lifted
            once = either (error . show) id $ Lowering.lift composite evenValue
            twice = either (error . show) id $ Lowering.lift lowering evenValue >>= Lowering.lift upper
        within once `shouldBe` within twice

    it "compose: reject an expansion that applies an earlier constructor to the wrong number of children" $ do
        -- Lowering twice gives Nothing for these terms, so no composite agrees with it.
        let upper arity expansion = either (error . show) id $ Lowering.mkLowering [("quad", arity, expansion)]
            fewer = upper 1 $ Apply "double" []
            more = upper 2 $ Apply "double" [Child 0, Child 1]
        Lowering.compose fewer lowering `shouldBe` Left (WrongArity "double" 1 0)
        Lowering.compose more lowering `shouldBe` Left (WrongArity "double" 1 2)
        (Lowering.lower fewer >=> Lowering.lower lowering) (Node "quad" [one]) `shouldBe` Nothing
        (Lowering.lower more >=> Lowering.lower lowering) (Node "quad" [one, zero]) `shouldBe` Nothing

    it "accept a later grammar whose productions lower into the earlier grammar" $
        Lowering.checkLowering lowering earlier later `shouldBe` []

    it "report a production that does not lower" $ do
        let wrong = either (error . show) id $ Lowering.mkLowering [("double", 1, Apply "mul" [Child 0, Child 0])]
        Lowering.checkLowering wrong earlier (grammar [("double", 1)]) `shouldBe` [NotLowered () "double" [()]]

    it "reject an expansion with a child out of range" $
        Lowering.mkLowering [("double", 1, Apply "add" [Child 0, Child 1 :: Expansion Symbol])]
            `shouldBe` Left (ChildOutOfRange "double" 1)

    it "lift a source grammar to the terms that it accepts and whose lowering a target accepts"
        $ checkCoverage
        $ forAll genLiftCase liftFromAgrees
  where
    zero = Node "zero" []
    one = Node "one" []
    add left right = Node "add" [left, right]
    double term = Node "double" [term]
    successor term = Node "succ" [term]

-- | @double(x) -> add(x, x)@ copies its child; @succ(x) -> add(x, one)@ does not.
lowering :: Lowering.Lowering Symbol
lowering =
    either (error . show) id $
        Lowering.mkLowering
            [ ("double", 1, Apply "add" [Child 0, Child 0])
            , ("succ", 1, Apply "add" [Child 0, Apply "one" []])
            ]

-- | Sums of zero and one.
earlier :: FTA.PlainFTA () Symbol
earlier = grammar []

-- | Sums of zero and one, with double and succ.
later :: FTA.PlainFTA () Symbol
later = grammar [("double", 1), ("succ", 1)]

-- | One state with zero, one, add, and the given constructors over that state.
grammar :: [(Symbol, Int)] -> FTA.PlainFTA () Symbol
grammar extra =
    either (error . show) id $
        FTA.mkFTA
            ()
            [ ((),) $
                [ FTA.Transition "zero" [] noConstraint
                , FTA.Transition "one" [] noConstraint
                , FTA.Transition "add" [(), ()] noConstraint
                ]
                    <> [FTA.Transition symbol (replicate arity ()) noConstraint | (symbol, arity) <- extra]
            ]

-- | The sums of zero and one whose value is even.
evenValue :: FTA.PlainFTA Parity Symbol
evenValue =
    either (error . show) id $
        FTA.mkFTA
            Even
            [ (Even, [leaf "zero", sum' Even Even, sum' Odd Odd])
            , (Odd, [leaf "one", sum' Even Odd, sum' Odd Even])
            ]
  where
    leaf symbol = FTA.Transition symbol [] noConstraint
    sum' left right = FTA.Transition "add" [left, right] noConstraint

-- | A lowering, the rows of a source table, and the rows of a target table.
type LiftCase = ([(Symbol, Int, Expansion Symbol)], Rows, Rows)

-- | The transitions of each state of a table with states 0, 1, and so on.
type Rows = [(Int, [FTA.Transition Int Symbol Constraint])]

-- | The symbols that an expansion can use, with their arities.
baseSymbols :: [(Symbol, Int)]
baseSymbols = [("a", 0), ("b", 0), ("g", 1), ("f", 2)]

-- | The new constructors, with their arities.
newSymbols :: [(Symbol, Int)]
newSymbols = [("n", 2), ("m", 1), ("k", 2)]

-- | An expansion of the given depth at most, with the children of a constructor with the given arity as leaves.
genExpansion :: Int -> Int -> Gen (Expansion Symbol)
genExpansion arity depth
    | depth == 0 = child
    | otherwise = frequency [(1, child), (3, apply)]
  where
    child = Child <$> choose (0, arity - 1)
    -- A symbol with more children is more frequent, so that an expansion has several leaves.
    apply = do
        (symbol, n) <- frequency [(n + 1, pure (symbol, n)) | (symbol, n) <- baseSymbols]
        Apply symbol <$> vectorOf n (genExpansion arity (depth - 1))

-- | A table with the given number of states and of transitions for each state. Pairs of children can have an equality.
genRows :: Int -> Int -> [(Symbol, Int)] -> Bool -> Gen Rows
genRows states perState symbols withEquality = mapM row [0 .. states - 1]
  where
    row state = (,) state . nub <$> vectorOf perState transition
    transition = do
        (symbol, n) <- elements symbols
        children <- vectorOf n $ choose (0, states - 1)
        constraint <- frequency [(if withEquality && n == 2 then 1 else 0, pure equal), (2, pure noConstraint)]
        pure $ FTA.Transition symbol children constraint
    equal = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]

-- | A lowering of the new constructors, a source table over all symbols, and a target table over the base symbols.
genLiftCase :: Gen LiftCase
genLiftCase =
    (,,)
        <$> mapM (\(symbol, arity) -> (,,) symbol arity <$> genExpansion arity 3) newSymbols
        <*> genRows 2 5 (baseSymbols <> newSymbols) True
        <*> genRows 3 4 baseSymbols False

-- | The terms over the symbols with at most the given number of nodes.
termsUpTo :: Int -> [(Symbol, Int)] -> [Term Symbol]
termsUpTo bound symbols = concatMap sized [1 .. bound]
  where
    sized n = [Node symbol kids | (symbol, arity) <- symbols, kids <- forest arity (n - 1)]
    forest 0 0 = [[]]
    forest 0 _ = []
    forest k n = [t : rest | m <- [1 .. n - (k - 1)], t <- sized m, rest <- forest (k - 1) (n - m)]

-- | The terms that the lifted automaton and the specification are compared on.
comparedTerms :: [Term Symbol]
comparedTerms = termsUpTo 5 (baseSymbols <> newSymbols)

{- | The lifted automaton accepts a term exactly when the source accepts it and the target accepts its lowering.
The counterexample shows the first term with two different verdicts.
-}
liftFromAgrees :: LiftCase -> Property
liftFromAgrees (entries, sourceRows, targetRows) =
    case built of
        Left failure -> counterexample ("invalid case: " <> failure) False
        Right (lowering', source, target) -> case Lowering.liftFrom lowering' source (FTA.mapConstraints (const ()) target) of
            Left failure -> counterexample ("liftFrom failed: " <> show failure) False
            Right lifted ->
                let verdict term =
                        ( FTA.accepts lifted term
                        , FTA.accepts source term && maybe False (FTA.accepts target) (Lowering.lower lowering' term)
                        )
                    differing = [(term, got, want) | term <- comparedTerms, let (got, want) = verdict term, got /= want]
                    accepted = [got | term <- comparedTerms, FTA.accepts source term, let (got, _) = verdict term]
                 in cover 50 (or accepted && not (and accepted)) "the lifted automaton accepts some and rejects some terms of the source" $
                        cover 30 (any copies entries) "an expansion uses a child two times" $
                            cover 30 (any drops entries) "an expansion drops a child" $
                                cover 30 (any single entries) "an expansion is one child" $
                                    case differing of
                                        [] -> property True
                                        (term, got, want) : _ ->
                                            counterexample ("first difference: " <> show term <> ", lifted " <> show got <> ", specification " <> show want) False
  where
    built =
        (,,)
            <$> fromError (Lowering.mkLowering entries)
            <*> fromError (FTA.mkFTA 0 sourceRows)
            <*> fromError (FTA.mkFTA 0 targetRows)
    fromError :: (Show e) => Either e a -> Either String a
    fromError = either (Left . show) Right
    copies (_, _, expansion) = let used = indices expansion in length used /= length (nub used)
    drops (_, arity, expansion) = length (nub $ indices expansion) < arity
    single (_, _, expansion) = case expansion of
        Child _ -> True
        Apply _ _ -> False
    indices (Child index) = [index]
    indices (Apply _ parts) = concatMap indices parts
