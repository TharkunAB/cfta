{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

{- | Tests of "Data.CFTA.Gen.Refinement.Derive": the derived generators of
SortedLists, SafeDivision, and LiquidPairs have the cardinality and the ranks
of the hand-written generators of the examples.
-}
module Data.CFTA.Gen.Refinement.DeriveSpec (spec) where

-- A measure names each child, as in \x _ -> x, as a contract does.
{- HLINT ignore "Use const" -}

import Control.Monad (forM_, void)
import Data.Containers.ListUtils (nubOrd)
import GHC.Generics (Generic)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import Data.CFTA.Gen.Refinement.Derive
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Index (Arity (..), Cardinality (..), Rank (..))
import Data.CFTA.Refinement.Expression (Expr, Refinement)
import Data.CFTA.Refinement.Symbolic (Symbolic (..), true, (.&&))

-- | A list that its invariant keeps sorted.
data SortedList = Nil | Cons Integer SortedList
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The measure is the head. The head of the empty list is above every element.
instance HasLTA SortedList where
    invariant = Measured headOf sorted

-- | The head of a sorted list.
headOf :: (Symbolic e) => SortedList -> [e] -> e
headOf Cons{} [x, _] = x
headOf _ _ = 1000001

-- | Each element is from zero to a million, and at most the head of the rest.
sorted :: (Symbolic e) => SortedList -> [e] -> Truth e
sorted Cons{} [x, restHead] = 0 .<= x .&& x .<= 1000000 .&& x .<= restHead
sorted _ _ = true

-- | The elements of a sorted list.
toList :: SortedList -> [Integer]
toList Nil = []
toList (Cons element rest) = element : toList rest

-- | The hand-written sorted lists of SortedLists.hs.
sortedLists :: LTAGen.LTAGen [Integer]
sortedLists = LTAGen.recurUpTo 8 $ \rest -> LTAGen.oneof [nil, cons rest]
  where
    nil = LTAGen.leaf [] "nil" (.== 1000001)
    cons rest =
        LTAGen.measured
            "cons"
            (\element restHead -> element .<= restHead)
            (\element _ -> element)
            $ LTAGen.do
                element <- LTAGen.every `LTAGen.satisfying` (\v -> 0 .<= v .&& v .<= 1000000)
                elements <- rest
                LTAGen.pure (element : elements)

-- | The annotations of the sorted lists of the builtin list type.
listAnnotations :: [(String, Annotation)]
listAnnotations =
    [ ("[]", measure (1000001 :: Expr))
    , (":", contract (\x restHead -> 0 .<= x .&& x .<= 1000000 .&& x .<= restHead) <> measure (\x _ -> x))
    ]

-- | A division of twelve by a denominator that is not zero.
newtype Division = Divide Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The denominator is from zero to five, and it is not zero.
instance HasLTA Division where
    invariant = Contracted nonZero
      where
        nonZero _ [d] = 0 .<= d .&& d .<= 5 .&& d ./= 0
        nonZero _ _ = true

-- | The hand-written divisions of SafeDivision.hs.
divisions :: LTAGen.LTAGen (Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    d <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (d, 12 `div` d)

-- | A pair whose left value is below its right value.
data Pair = Pair Integer Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | The left value is below the right value.
instance HasLTA Pair where
    invariant = Contracted below
      where
        below _ [left, right] = left .< right
        below _ _ = true

-- | Values that the solver knows only by the range that contains them.
ranged :: [(Integer, Refinement)]
ranged =
    [ (1, \v -> 0 .<= v .&& v .< 2)
    , (3, \v -> 2 .<= v .&& v .< 4)
    , (5, \v -> 4 .<= v .&& v .< 6)
    ]

-- | The hand-written pairs of LiquidPairs.hs.
pairs :: LTAGen.LTAGen (Integer, Integer)
pairs = LTAGen.guarded "pair" (\left right -> left .< right) $ LTAGen.do
    left <- LTAGen.pool ranged
    right <- LTAGen.pool ranged
    LTAGen.pure (left, right)

{- | Compile both generators, and expect the same cardinality and the same
value at each checked rank: every rank of a small generator, and the first
three, the middle, the last two, and 200 ranks of a fixed sequence of a large
one.
-}
sameRanks :: (Eq a, Show a) => LTAGen.LTAGen a -> Either DeriveLTAError (LTAGen.LTAGen a) -> Expectation
sameRanks handWritten derived = case derived of
    Left err -> expectationFailure $ show err
    Right generator -> do
        expected <- LTAGen.compile handWritten
        actual <- LTAGen.compile generator
        LTAGen.cardinality actual `shouldBe` LTAGen.cardinality expected
        case LTAGen.cardinality expected of
            Left err -> expectationFailure $ show err
            Right (Cardinality total) -> do
                let next rank = (rank * 6364136223846793005 + 1442695040888963407) `mod` total
                    checked
                        | total <= 100000 = [0 .. total - 1]
                        | otherwise = nubOrd $ [0, 1, 2, total `div` 2, total - 2, total - 1] <> take 200 (iterate next 1)
                forM_ checked $ \rank -> LTAGen.unrank actual (Rank rank) `shouldBe` LTAGen.unrank expected (Rank rank)

spec :: Spec
spec = describe "Data.CFTA.Gen.Refinement.Derive" $ do
    it "derives SortedLists from annotations with the ranks of the hand-written generator"
        $ sameRanks sortedLists
        $ deriveLTAWith @[Integer] 8 (atom @Integer LTAGen.every) listAnnotations
    it "derives SortedLists from a HasLTA instance with the ranks of the hand-written generator"
        $ sameRanks sortedLists
        $ fmap toList <$> deriveLTA @SortedList 8 (atom @Integer LTAGen.every)
    it "derives SafeDivision from a HasLTA instance with the ranks of the hand-written generator"
        $ sameRanks divisions
        $ fmap (\(Divide d) -> (d, 12 `div` d)) <$> deriveLTA @Division 0 (atom @Integer (LTAGen.elements [0 .. 5]))
    it "derives LiquidPairs from a HasLTA instance with the ranks of the hand-written generator"
        $ sameRanks pairs
        $ fmap (\(Pair left right) -> (left, right)) <$> deriveLTA @Pair 0 (atom @Integer (LTAGen.pool ranged))
    it "gives the formulas of the annotations from the functions of the invariant" $ do
        let formulas annotations = [(name, annotationFormulas annotation) | (name, annotation) <- annotations]
        formulas (invariantAnnotations (invariant @SortedList))
            `shouldBe` formulas (zip ["Nil", "Cons"] (map snd listAnnotations))
    it "checks values with the functions of the invariant" $ do
        let atoms = atom @Integer LTAGen.every
            rules = invariant @SortedList
        map (holds atoms rules) [Cons 1 (Cons 2 (Cons 2 Nil)), Cons 3 (Cons 1 Nil), Cons 2000000 Nil]
            `shouldBe` [True, False, False]
        map (measureOf atoms rules) [Cons 4 (Cons 5 Nil), Nil] `shouldBe` [Just 4, Just 1000001]
    it "reports annotations that do not fit the datatype" $ do
        let derive annotations = void $ deriveLTAWith @SortedList 8 (atom @Integer LTAGen.every) annotations
        derive [("Cosn", mempty)] `shouldBe` Left (UnknownConstructors ["Cosn"] ["Nil", "Cons"])
        derive [("Cons", contract (\x -> x .<= 1))] `shouldBe` Left (AnnotationArityMismatch "Cons" (Arity 2) (Arity 1))
        derive [("Cons", measure (\x _ -> x) <> measure (\_ y -> y))] `shouldBe` Left (SeveralMeasures "Cons")
        derive [("Nil", contract (0 .<= (1 :: Expr)))] `shouldBe` Left (ContractWithoutFields "Nil")
        void (deriveLTAWith @SortedList 8 mempty []) `shouldSatisfy` either isMissingAtom (const False)
  where
    isMissingAtom (MissingAtom _) = True
    isMissingAtom _ = False
