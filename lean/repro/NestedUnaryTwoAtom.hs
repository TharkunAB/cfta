module Main (main) where

import Control.Monad (foldM, unless)
import Data.Bits (bit, testBit, (.&.), (.|.))
import Data.CFTA.Constraint (Constraint, Guard (..), conjoinConstraints, noConstraint, semanticConstraint)
import qualified Data.CFTA.Equality as E
import Data.CFTA.Interned.Operations (mergeAlternatives)

-- | Generate the admitted conjunction rows from two source residual atoms.
guards :: [Constraint]
guards = [noConstraint, a, b, conjoinConstraints a b]
  where
    a = semanticConstraint (Not Top)
    b = semanticConstraint (Not Bottom)

-- | Build one nested endpoint from its selected generated rows.
endpoint :: Int -> E.Node String
endpoint bits = E.Node [E.Edge "f" [E.Node [E.mkEdge "a" [] (guards !! row)]] | row <- [0 .. 3], testBit bits row]

-- | Retain distinct unary ancestor occurrences.
context :: String -> [Int] -> E.Node String
context tag rows = E.Node [E.Edge (tag ++ show index) [endpoint row] | (index, row) <- zip [0 ..] rows]

-- | Put the two projected contexts in their original forest positions.
forest :: ([Int], [Int]) -> [E.Node String]
forest (left, right) = [context "l" left, context "r" right]

-- | Preserve whole-endpoint identity before the generated Cartesian product.
meet :: Int -> Int -> Int
meet left right
    | left == right = left
    | otherwise = foldr (.|.) 0 [bit (a .|. b) | a <- [0 .. 3], b <- [0 .. 3], testBit left a, testBit right b]

-- | Read both projected targets before either side changes.
step :: ([Int], [Int]) -> ([Int], [Int])
step (left, right) = (map (meet (foldr (.|.) 0 right)) left, map (meet (foldr (.|.) 0 left)) right)

-- | Compare each source pass with its generated row transition.
check :: Int -> ([Int], [Int]) -> IO Int
check pass groups@(left, right) = do
    let next = step groups
        eqs = E.mkEqConstraints [[E.path [0, 0], E.path [1, 0]]]
        actual = E.reduceEqConstraints eqs E.EmptyConstraints (forest groups)
    unless (all (\mask -> mergeAlternatives (endpoint mask) == endpoint mask) (left ++ right)) $
        fail "Nested target merge changed a generated endpoint"
    unless (actual == forest next) $ fail ("Nested source schedule mismatch " ++ show (pass, groups, next))
    if next == groups
        then pure pass
        else
            if pass > 4 * (length left + length right) + 2
                then fail "Exceeded generated carrier bound"
                else check (pass + 1) next

-- | Check singleton groups and deterministic groups with three occurrences.
main :: IO ()
main = do
    let sample seed = (map (pick seed) [0 .. 2], map (pick (seed * 19 + 7)) [0 .. 2])
        pick seed position = ((seed * (11 + 2 * position) + position * position * 7) `div` (position + 1)) .&. 15
        cases = [([a], [b]) | a <- [0 .. 15], b <- [0 .. 15]] ++ map sample [0 .. 4095]
    longest <- foldM (\old groups -> max old <$> check 0 groups) 0 cases
    print ("nested-two-atom", length cases, "maximum-changing-passes", longest)
