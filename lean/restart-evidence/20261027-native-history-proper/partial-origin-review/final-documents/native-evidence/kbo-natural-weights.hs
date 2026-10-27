{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Bits (finiteBitSize)
import Data.CFTA.Symbol (Symbol (..))
import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Specftacular.Rewriting
import Specftacular.Types
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Read (readMaybe)

-- | Use one concrete type for the public order comparison.
baseType :: Term
baseType = typeSkeletonToTerm (TCons "Int" [])

-- | Make a typed constant leaf.
leaf :: Symbol -> Term
leaf symbol = Term symbol [baseType]

-- | Put the argument in one well-typed application context.
context :: Term -> Term
context argument =
    Term "app" [baseType, Term "c" [typeSkeletonToTerm (TFun (TCons "Int" []) (TCons "Int" []))], argument]

-- | Check the actual public comparator and actual public rewrite guard.
contextOverflow :: IO ()
contextOverflow = do
    let weights = Map.fromList [("a", fromIntegral (maxBound :: Int)), ("b", 0), ("c", 1)]
        smaller = leaf "a"
        larger = leaf "b"
        baseComparison = kboCompare weights (const False) smaller larger
        contextComparison = kboCompare weights (const False) (context smaller) (context larger)
        law = Term "(==)" [baseType, smaller, larger]
        rules = addLawRules Map.empty law (emptyRules (KnuthBendix weights))
        localRewrite = reducible (const False) rules (context smaller)
        nonnegative = all (>= 0) (Map.elems weights)
    print ("intBits", finiteBitSize (0 :: Int))
    print ("allMapEntriesNonnegative", nonnegative)
    print ("leafComparison", baseComparison)
    print ("sameApplicationContextComparison", contextComparison)
    print ("localRewriteAcceptedInContext", localRewrite)
    unless (nonnegative && baseComparison == GT && contextComparison == GT && localRewrite) exitFailure

-- | Give one distinct symbol to each syntactic definition.
name :: Int -> Symbol
name index = Symbol ("c" <> T.justifyRight 3 '0' (T.pack (show index)))

-- | Construct a rule c_i x = c_previous c_previous with consistent occurrence types.
definition :: Int -> Term
definition index = Term "(==)" [functionTypeTerm, lhs, rhs]
  where
    scalar = TCons "Int" []
    functionTypeTerm = typeSkeletonToTerm (TFun scalar scalar)
    previous = if index == 0 then "b" else name (index - 1)
    previousType = TFun scalar (TFun scalar scalar)
    outerType = TFun previousType (TFun scalar scalar)
    lhs = Term "app" [functionTypeTerm, Term (name index) [typeSkeletonToTerm previousType], leaf "<v>x"]
    rhs = Term "app" [functionTypeTerm, Term previous [typeSkeletonToTerm outerType], Term previous [typeSkeletonToTerm previousType]]

-- | Check actual computed weights against exact integers through the tested depth.
computedGrowth :: Int -> IO ()
computedGrowth depth = do
    let rules = foldl' (\current index -> addLawRules Map.empty (definition index) current)
            (emptyRules (KnuthBendix Map.empty)) [0 .. depth]
        weights = definitionWeights rules
    mapM_ (\index -> do
        let actual = Map.lookup (name index) weights
            expected = (2 :: Integer) ^ (index + 1) - 1
        print (index, actual, expected)
        unless (fmap toInteger actual == Just expected) exitFailure) [0 .. depth]

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        [] -> contextOverflow
        ["computed", value]
            | Just depth <- readMaybe value
            , depth >= 0
            , depth <= 63 -> computedGrowth depth
        _ -> fail "usage: kbo-int-weights [computed DEPTH], with DEPTH from 0 to 63"
