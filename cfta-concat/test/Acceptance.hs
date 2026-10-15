{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

{- | The predicates and measures of four generator examples as plain Haskell.

For SortedLists, SafeDivision, LiquidPairs, and RedBlackTrees of
@cfta-generator/examples@, the plugin compiles the predicates and the measures
with 'symbolic'. The test checks:

1. Each compiled formula or term is equal to the one of the expression
   language in the example, and it shows as the same text.
2. The generator with the compiled formulas has the cardinality of the
   generator of the example, and the same value at each checked rank: every
   rank of a generator with at most 100000 members, and otherwise the first
   three, the middle one, the last two, and 200 ranks from a fixed sequence.
3. The same Haskell functions hold on the values at the checked ranks.

Each check forces a compiled formula, so a call that the plugin leaves in the
program fails the test.
-}
module Main (main) where

-- The measures name each child, as the measures of the examples do.
{- HLINT ignore "Use const" -}
-- The lambda of halfOpen gives it two parameters, so that it inlines with two.
{- HLINT ignore halfOpen "Redundant lambda" -}

import Control.Monad (unless)
import Data.Containers.ListUtils (nubOrd)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.Maybe (isJust)
import System.Exit (exitFailure)

import qualified Data.CFTA.Gen.Do as LTAGen
import Data.CFTA.Gen.Refinement (LTAGen)
import qualified Data.CFTA.Gen.Refinement as LTAGen
import Data.CFTA.Index (Cardinality (..), Depth, Rank (..))
import Data.CFTA.Refinement.Expression (Expr, Formula, Refinement, refinementFormula, (.&&), (./=), (.<), (.<=), (.==))
import Data.CFTA.Refinement.Guard (contractFormulaFrom, measureTermFrom)

import ConCat.Rebox ()
import Data.CFTA.Concat (symbolic)

-- * SortedLists

-- | The range of an element.
inRange :: Integer -> Bool
inRange v = 0 <= v && v <= 1000000
{-# INLINE inRange #-}

-- | The measure of the empty list: above every element.
nilHead :: Integer -> Bool
nilHead v = v == 1000001
{-# INLINE nilHead #-}

-- | The element is at most the head of the rest.
ordered :: Integer -> Integer -> Bool
ordered element restHead = element <= restHead
{-# INLINE ordered #-}

-- | The measure of a non-empty list: its head.
listHead :: Integer -> Integer -> Integer
listHead element _ = element
{-# INLINE listHead #-}

-- | The formulas of a sorted-list generator.
data ListFormulas = ListFormulas
    { elementRange :: Refinement
    , emptyHead :: Refinement
    , order :: Expr -> Expr -> Formula
    , headMeasure :: Expr -> Expr -> Expr
    }

-- | The formulas of @examples/SortedLists.hs@.
handWrittenLists :: ListFormulas
handWrittenLists =
    ListFormulas
        { elementRange = \v -> 0 .<= v .&& v .<= 1000000
        , emptyHead = (.== 1000001)
        , order = \element restHead -> element .<= restHead
        , headMeasure = \element _ -> element
        }

-- | The compiled formulas.
compiledLists :: ListFormulas
compiledLists =
    ListFormulas
        { elementRange = symbolic inRange
        , emptyHead = symbolic nilHead
        , order = symbolic ordered
        , headMeasure = symbolic listHead
        }

-- | The generator of @examples/SortedLists.hs@ with the given formulas.
sortedLists :: ListFormulas -> LTAGen [Integer]
sortedLists formulas = LTAGen.recurUpTo 8 $ \rest -> LTAGen.oneof [nil, cons rest]
  where
    nil = LTAGen.leaf [] "nil" (emptyHead formulas)
    cons rest =
        LTAGen.measured "cons" (order formulas) (headMeasure formulas) $ LTAGen.do
            x <- LTAGen.every `LTAGen.satisfying` elementRange formulas
            xs <- rest
            LTAGen.pure (x : xs)

-- | Whether a list is in the language of SortedLists, by the same Haskell functions.
sortedList :: [Integer] -> Bool
sortedList xs = all inRange xs && and (zipWith ordered xs (drop 1 xs)) && length xs <= 8

-- * SafeDivision

-- | A denominator is not zero.
nonZero :: Integer -> Bool
nonZero v = v /= 0
{-# INLINE nonZero #-}

-- | The divisions of @examples/SafeDivision.hs@ with a condition on the denominator.
divisions :: Refinement -> LTAGen (Integer, Integer)
divisions denominator = LTAGen.node "divide" $ LTAGen.do
    d <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` denominator
    LTAGen.pure (d, 12 `div` d)

-- * LiquidPairs

{- | A value in a half-open range. The bounds are values at run time, so the
plugin makes them constants of the category. The lambda gives the function
two parameters, so that it inlines when it gets the two bounds.
-}
halfOpen :: Integer -> Integer -> Integer -> Bool
halfOpen low high = \v -> low <= v && v < high
{-# INLINE halfOpen #-}

-- | The left value is below the right value.
below :: Integer -> Integer -> Bool
below left right = left < right
{-# INLINE below #-}

-- | The pool of @examples/LiquidPairs.hs@ with a refinement for each range.
ranged :: (Integer -> Integer -> Refinement) -> [(Integer, Refinement)]
ranged range = [(1, range 0 2), (3, range 2 4), (5, range 4 6)]

-- | The range refinement of @examples/LiquidPairs.hs@.
handWrittenRange :: Integer -> Integer -> Refinement
handWrittenRange low high v = fromInteger low .<= v .&& v .< fromInteger high

-- | The compiled range refinement.
compiledRange :: Integer -> Integer -> Refinement
compiledRange low high = symbolic (halfOpen low high)

-- | The pairs of @examples/LiquidPairs.hs@ with a contract and a pool.
pairs :: (Expr -> Expr -> Formula) -> [(Integer, Refinement)] -> LTAGen (Integer, Integer)
pairs pairContract values = LTAGen.guarded "pair" pairContract $ LTAGen.do
    left <- LTAGen.pool values
    right <- LTAGen.pool values
    LTAGen.pure (left, right)

-- * RedBlackTrees

-- | The shape of a red-black tree, as in @examples/RedBlackTrees.hs@.
data Tree = Leaf | Black Tree Tree | Red Tree Tree
    deriving (Eq, Show)

-- | A leaf has black height zero.
leafHeight :: Integer -> Bool
leafHeight v = v == 0
{-# INLINE leafHeight #-}

-- | The two subtrees have equal black heights.
balanced :: Integer -> Integer -> Bool
balanced leftHeight rightHeight = leftHeight == rightHeight
{-# INLINE balanced #-}

-- | A black node adds one to the black height.
blackHeight :: Integer -> Integer -> Integer
blackHeight leftHeight _ = leftHeight + 1
{-# INLINE blackHeight #-}

-- | A red node keeps the black height.
redHeight :: Integer -> Integer -> Integer
redHeight leftHeight _ = leftHeight
{-# INLINE redHeight #-}

{- | The black height of a tree whose nodes satisfy the contract, by the same
Haskell functions. The colors of the children are in the grammar, not in the
contract.
-}
blackHeightOf :: Tree -> Maybe Integer
blackHeightOf Leaf = if leafHeight 0 then Just 0 else Nothing
blackHeightOf (Black left right) = node blackHeight left right
blackHeightOf (Red left right) = node redHeight left right

-- | The measure of a node whose children satisfy the contract.
node :: (Integer -> Integer -> Integer) -> Tree -> Tree -> Maybe Integer
node measure left right = do
    leftHeight <- blackHeightOf left
    rightHeight <- blackHeightOf right
    if balanced leftHeight rightHeight then Just (measure leftHeight rightHeight) else Nothing

-- | The formulas of a red-black tree generator.
data TreeFormulas = TreeFormulas
    { leafRefinement :: Refinement
    , balance :: Expr -> Expr -> Formula
    , blackMeasure :: Expr -> Expr -> Expr
    , redMeasure :: Expr -> Expr -> Expr
    }

-- | The formulas of @examples/RedBlackTrees.hs@.
handWrittenTrees :: TreeFormulas
handWrittenTrees =
    TreeFormulas
        { leafRefinement = (.== 0)
        , balance = \leftHeight rightHeight -> leftHeight .== rightHeight
        , blackMeasure = \leftHeight _ -> leftHeight + 1
        , redMeasure = \leftHeight _ -> leftHeight
        }

-- | The compiled formulas.
compiledTrees :: TreeFormulas
compiledTrees =
    TreeFormulas
        { leafRefinement = symbolic leafHeight
        , balance = symbolic balanced
        , blackMeasure = symbolic blackHeight
        , redMeasure = symbolic redHeight
        }

-- | The generator of @examples/RedBlackTrees.hs@ with the given formulas.
redBlackTrees :: TreeFormulas -> Depth -> LTAGen Tree
redBlackTrees formulas bound = LTAGen.recurUpTo bound $ \blackRooted ->
    let anyRooted = LTAGen.oneof [blackRooted, red blackRooted]
     in LTAGen.oneof [leaf, black anyRooted]
  where
    leaf = LTAGen.leaf Leaf "leaf" (leafRefinement formulas)
    black child = LTAGen.measured "black" (balance formulas) (blackMeasure formulas) (Black <$> child <*> child)
    red child = LTAGen.measured "red" (balance formulas) (redMeasure formulas) (Red <$> child <*> child)

-- * Checks

-- | Record a failure, and print the outcome of a check.
check :: IORef Bool -> String -> Bool -> String -> IO ()
check failed name ok detail = do
    unless ok $ modifyIORef' failed (const True)
    putStrLn $ (if ok then "ok    " else "FAIL  ") <> name <> ": " <> detail

-- | A compiled value is equal to the hand-written one, and it shows as the same text.
same :: (Eq a, Show a) => IORef Bool -> String -> a -> a -> IO ()
same failed name compiled handWritten =
    check failed name (compiled == handWritten && show compiled == show handWritten) $
        show compiled <> (if compiled == handWritten then "" else ", hand-written: " <> show handWritten)

{- | The generator with the compiled formulas has the cardinality of the
hand-written generator, the same value at each checked rank, and values that
the predicate accepts.
-}
sameRanks :: (Eq a) => IORef Bool -> String -> (a -> Bool) -> LTAGen a -> LTAGen a -> IO ()
sameRanks failed name accepted handWritten compiled = do
    hand <- LTAGen.compile handWritten
    actual <- LTAGen.compile compiled
    let expected = LTAGen.cardinality hand
    check failed (name <> " cardinality") (LTAGen.cardinality actual == expected) (show expected)
    case expected of
        Right (Cardinality total) -> do
            let next rank = (rank * 6364136223846793005 + 1442695040888963407) `mod` total
                ranks
                    | total <= 100000 = [0 .. total - 1]
                    | otherwise = nubOrd $ [0, 1, 2, total `div` 2, total - 2, total - 1] <> take 200 (iterate next 1)
                differing = [rank | rank <- ranks, LTAGen.unrank actual (Rank rank) /= LTAGen.unrank hand (Rank rank)]
                rejected = [rank | rank <- ranks, either (const True) (not . accepted) (LTAGen.unrank actual (Rank rank))]
            check failed (name <> " ranks") (null differing) $
                "equal at " <> show (length ranks) <> " ranks" <> concat [", differs at " <> show rank | rank <- take 1 differing]
            check failed (name <> " values") (null rejected) $
                "the predicate holds at " <> show (length ranks - length rejected) <> " ranks"
        Left problem -> check failed (name <> " ranks") False (show problem)

main :: IO ()
main = do
    failed <- newIORef False
    -- SortedLists
    same
        failed
        "SortedLists element range"
        (refinementFormula (elementRange compiledLists))
        (refinementFormula (elementRange handWrittenLists))
    same
        failed
        "SortedLists empty head"
        (refinementFormula (emptyHead compiledLists))
        (refinementFormula (emptyHead handWrittenLists))
    same
        failed
        "SortedLists order"
        (contractFormulaFrom 0 (order compiledLists))
        (contractFormulaFrom 0 (order handWrittenLists))
    same
        failed
        "SortedLists head"
        (measureTermFrom 0 (headMeasure compiledLists))
        (measureTermFrom 0 (headMeasure handWrittenLists))
    sameRanks failed "SortedLists" sortedList (sortedLists handWrittenLists) (sortedLists compiledLists)
    -- SafeDivision
    same failed "SafeDivision denominator" (refinementFormula (symbolic nonZero)) (refinementFormula (./= 0))
    sameRanks
        failed
        "SafeDivision"
        (\(d, q) -> nonZero d && q == 12 `div` d)
        (divisions (./= 0))
        (divisions (symbolic nonZero))
    -- LiquidPairs
    mapM_
        ( \(low, high) ->
            same
                failed
                ("LiquidPairs range " <> show (low, high))
                (refinementFormula (compiledRange low high))
                (refinementFormula (handWrittenRange low high))
        )
        [(0, 2), (2, 4), (4, 6)]
    same
        failed
        "LiquidPairs below"
        (contractFormulaFrom 0 (symbolic below))
        (contractFormulaFrom 0 (\left right -> left .< right))
    sameRanks
        failed
        "LiquidPairs"
        (uncurry below)
        (pairs (.<) (ranged handWrittenRange))
        (pairs (symbolic below) (ranged compiledRange))
    -- RedBlackTrees
    same
        failed
        "RedBlackTrees leaf"
        (refinementFormula (leafRefinement compiledTrees))
        (refinementFormula (leafRefinement handWrittenTrees))
    same
        failed
        "RedBlackTrees balance"
        (contractFormulaFrom 0 (balance compiledTrees))
        (contractFormulaFrom 0 (balance handWrittenTrees))
    same
        failed
        "RedBlackTrees black"
        (measureTermFrom 0 (blackMeasure compiledTrees))
        (measureTermFrom 0 (blackMeasure handWrittenTrees))
    same
        failed
        "RedBlackTrees red"
        (measureTermFrom 0 (redMeasure compiledTrees))
        (measureTermFrom 0 (redMeasure handWrittenTrees))
    sameRanks
        failed
        "RedBlackTrees"
        (isJust . blackHeightOf)
        (redBlackTrees handWrittenTrees 3)
        (redBlackTrees compiledTrees 3)
    failures <- readIORef failed
    if failures then exitFailure else putStrLn "acceptance: all checks pass"
