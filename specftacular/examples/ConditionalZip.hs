{-# LANGUAGE OverloadedStrings #-}

-- | Discover and replay a conditional law for zip and unzip.
module Main (main) where

import Control.Monad (replicateM, unless)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA
import Data.CFTA.Refinement.Expression (Expr, Formula, true, (.==))
import Data.Dynamic (toDyn)
import Data.List (partition)
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Specftacular

-- | The input and result type of the proposed rewrite.
type Lists = ([Bool], [Bool])

-- | Its only generator constructs two lists whose lengths agree.
newtype SameLength = SameLength {lists :: Lists} deriving (Eq)

-- | Each list constructor stores the length of its result as its measure.
boundedLists :: Int -> LTA.LTAGen [Bool]
boundedLists limit
    | limit <= 0 = nil
    | otherwise =
        LTA.oneof
            [nil, LTA.measured "cons" consGuard consLength ((:) <$> LTA.elements [False, True] <*> boundedLists (limit - 1))]
  where
    nil = LTA.leaf [] "nil" (.== 0)
    consGuard :: Expr -> Expr -> Formula
    consGuard _ _ = true
    consLength :: Expr -> Expr -> Expr
    consLength _ tailLength = tailLength + 1

{- Note [The witness carries the condition]
------------------------------------------
Both projections take the same witness. A law over this type can use
their equal lengths. For a rewrite on plain lists, retain the set of
assignments checked after discovery. A pair outside that set has no rule.
-}

-- | Return the witnesses and a rewrite restricted to the verified domain.
discoverZip :: IO ([Lists], Lists -> Maybe Lists)
discoverZip = do
    let source = boundedLists 2
        equalLength :: Expr -> Expr -> Formula
        equalLength = (.==)
    joint <- LTA.compile (LTA.guarded "sameLength" equalLength (curry SameLength <$> source <*> source))
    witnesses <- either (fail . show) pure (LTA.values joint)
    let witnessType = typeSkeletonOf (Proxy :: Proxy SameLength)
        instanceFor ty
            | ty == witnessType =
                Just (generatedWith (DynGen (LTA.toGen joint)) (Just (toDyn ((==) :: SameLength -> SameLength -> Bool))))
            | otherwise = Nothing
        options = (defaultOptions 6 1){searchTests = 100, searchChecked = True}
    laws <-
        experimentalPhases
            options
            instanceFor
            [ con "left" (fst . lists)
            , con "right" (snd . lists)
            , con "lists" lists
            , con "zip" (zip :: [Bool] -> [Bool] -> [(Bool, Bool)])
            , con "unzip" (unzip :: [(Bool, Bool)] -> Lists)
            ]
    let checked = Set.fromList (map lists witnesses)
        valid (xs, ys) = unzip (zip xs ys) == (xs, ys)
    unless (any isZipLaw laws) $ fail ("missing conditional zip law: " ++ show laws)
    unless (not (Set.null checked) && all valid checked) $ fail "the equation failed exhaustive replay"
    let rewrite p
            | Set.member p checked = Just p
            | otherwise = Nothing
    pure (map lists witnesses, rewrite)

-- | Recognize either orientation of the discovered equation.
isZipLaw :: String -> Bool
isZipLaw law = case break (== "==") (drop 1 (words law)) of
    (lhs, "==" : rhs) -> matches lhs rhs || matches rhs lhs
    _ -> False
  where
    matches ["lists", w] rhs = unwords rhs == "unzip ((zip (left " ++ w ++ ")) (right " ++ w ++ "))"
    matches _ _ = False

-- | Compare the generated witness relation with all bounded list pairs.
main :: IO ()
main = do
    let lists = concatMap (`replicateM` [False, True]) [0 .. 2]
        pairs = [(xs, ys) | xs <- lists, ys <- lists]
        (inside, outside) = partition (\(xs, ys) -> length xs == length ys) pairs
        lhs (xs, ys) = unzip (zip xs ys)
    (witnesses, rewrite) <- discoverZip
    unless (length witnesses == 21 && Set.fromList witnesses == Set.fromList inside) $
        fail "the search did not discover the law on the 21 equal-length witnesses"
    unless (length outside == 28 && all (\p -> lhs p /= p && isNothing (rewrite p)) outside) $
        fail "the rewrite escaped to an unequal-length input"
    unless (all (\p -> rewrite p == Just (lhs p)) inside && isNothing (rewrite (replicate 3 True, replicate 3 False))) $
        fail "the rewrite escaped its checked domain"
    putStrLn "length xs == length ys && length xs <= 2 ==> unzip (zip xs ys) == (xs, ys)"
    putStrLn "All 21 equal-length pairs agree. All 28 unequal-length pairs refute the equation."
