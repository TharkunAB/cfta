{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Finite relational checks for explicitly tabled functions and a separate
permutation falsifier for a bounded carrier. The functions in the relation
check come from a closed signature, and the law test enumerates a finite set
of lists of a three-value type.
-}
module Main (main) where

import Control.Monad (replicateM, unless)
import Data.List (nub, permutations)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing, listToMaybe)
import qualified Data.Set as Set

import qualified Specftacular.FiniteLaw as F
import Specftacular.Types (A (A), apply, fromValue, toValue, pattern Term)

-- | A relation over the values of one carrier.
type Relation = Set.Set (Integer, Integer)

-- | Check the refined and erased arrow conditions for each function pair.
arrowPairs ::
    F.Operation -> [Integer] -> (Relation, Relation) -> (Relation, Relation) -> Map.Map (Integer, Integer) Bool
arrowPairs (F.Operation _ _ table) functions refined erased =
    Map.fromList
        [ ((f, g), preserves f g refined && preserves f g erased)
        | f <- functions
        , g <- functions
        ]
  where
    preserves f g (inputs, outputs) = all related inputs
      where
        related (x, y) = case (Map.lookup [f, x] table, Map.lookup [g, y] table) of
            (Just left, Just right) -> Set.member (left, right) outputs
            _ -> False

-- | Permutation images, the input, and the two observed results.
data Counterexample = Counterexample [A] [A] [A] [A] deriving (Eq, Show)

{- | Find a failed commuting square over bounded lists of three sampled
carrier values. Extend each permutation by fixing the other values.
-}
permutationCounterexample :: Int -> ([A] -> [A]) -> Maybe Counterexample
permutationCounterexample bound operation =
    listToMaybe
        [ Counterexample [zero, one, two] input renamedOutput outputFromRenamed
        | [zero, one, two] <- permutations carrier
        , let rename (A 0) = zero
              rename (A 1) = one
              rename (A 2) = two
              rename value = value
        , input <- inputs
        , let renamedOutput = map rename (operation input)
              outputFromRenamed = operation (map rename input)
        , renamedOutput /= outputFromRenamed
        ]
  where
    carrier = map A [0 .. 2]
    inputs = concat [replicateM n carrier | n <- [0 .. bound]]

-- | Check the finite arrow relations and the permutation falsifier.
main :: IO ()
main = do
    let num = Term "Signed3" []
        arrow = Term "Signed3Endomorphism" []
        higher = Term "EndomorphismOfSigned3Endomorphism" []
        values = [-1, 0, 1]
        functionIds = [0, 1, 2]
        classes =
            Map.fromList
                [(num, diagonalClasses values), (arrow, diagonalClasses functionIds), (higher, diagonalClasses functionIds)]
        absValue (A x) = A (abs x)
        functions = [(0, toValue (id :: A -> A)), (1, toValue absValue), (2, toValue (const (A 1) :: A -> A))]
        arguments = [(x, toValue (A $ fromInteger x)) | x <- values]
        applications =
            Map.fromList
                [ ([f, x], toInteger result)
                | (f, function) <- functions
                , (x, argument) <- arguments
                , let A result = fromValue (apply function argument)
                ]
        application = F.Operation [arrow, num] num applications
        replaceConstant x = if x == 2 then 0 else x
        higherApplication =
            F.Operation [higher, arrow] arrow $
                Map.fromList [([f, x], op x) | (f, op) <- [(0, id), (1, replaceConstant), (2, const 2)], x <- functionIds]
        identity = diagonal values
        nonnegative = diagonal [0, 1]
        full = arrowPairs application functionIds (nonnegative, identity) (identity, identity)
        onlyGuard = arrowPairs application functionIds (nonnegative, identity) (nonnegative, identity)
        equivalent = Set.fromList [(x, y) | x <- [0, 1], y <- [0, 1]]
        coarse = Set.insert (-1, -1) equivalent
        equalityOnPoints = arrowPairs application functionIds (nonnegative, identity) (coarse, coarse)
        cross = arrowPairs application functionIds (equivalent, identity) (coarse, coarse)
        truePairs = Map.keysSet . Map.filter id
        preservesZero = truePairs $ arrowPairs application functionIds (diagonal [0], diagonal [0]) (identity, identity)
        erasedArrow = truePairs full
        higherPairs = arrowPairs higherApplication functionIds (preservesZero, preservesZero) (erasedArrow, erasedArrow)
    _ <-
        either fail pure (F.finiteTheory classes $ Map.fromList [("apply", application), ("applyHigher", higherApplication)])
    check "id and abs agree on the admitted nonnegative values" (Map.lookup (0, 1) onlyGuard == Just True)
    check "the erased domain includes the negative counterexample" (Map.lookup (0, 1) full == Just False)
    check "the identity preserves the diagonal check" (Map.lookup (0, 0) equalityOnPoints == Just True)
    check
        "the identity fails a cross pair whose outputs the refined relation distinguishes"
        (Map.lookup (0, 0) cross == Just False)
    check "the next arrow layer reuses both relations on function values" $
        Map.lookup (0, 0) higherPairs == Just True && Map.lookup (0, 1) higherPairs == Just False
    putStrLn
        ( "Arrow checks retained "
            <> show (Map.size full)
            <> " ordered decisions at the first layer and "
            <> show (Map.size higherPairs)
            <> " at the next."
        )
    check "reverse commutes with every tested permutation" (isNothing $ permutationCounterexample 3 reverse)
    putStrLn "Reverse passes all 240 relabelings of A lists of length zero through three."
    let hiddenZero = permutationCounterexample 3 (filter (/= A 0))
    check "a hidden zero breaks commutation" (hiddenZero == Just (Counterexample [A 1, A 0, A 2] [A 0] [] [A 1]))
    putStrLn ("Hidden zero witness (images, input, rename after, rename before): " <> show hiddenZero)
    check "nub commutes with all the permutations" (isNothing $ permutationCounterexample 3 nub)
    let collapse _ = A 0
    check "nub fails under a non-injective map" (map collapse (nub [A 0, A 1]) /= nub (map collapse [A 0, A 1]))
    putStrLn "Nub passes the permutations and fails the many-to-one map."
  where
    diagonal values = Set.fromList [(value, value) | value <- values]
    diagonalClasses values = Map.fromList [(value, value) | value <- values]
    check label ok = unless ok (fail label)
