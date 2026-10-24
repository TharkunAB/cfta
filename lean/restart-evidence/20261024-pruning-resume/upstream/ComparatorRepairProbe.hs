{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Monad (unless)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Specftacular.Rewriting (TermOrder (PathOrder), termCompare)
import Specftacular.Types

-- Each constant uses the public signature and annotation APIs.
signature :: Sig
signature =
    con "f" ((\_ _ -> 0) :: A -> B -> Int)
        <> con "[]" ([] :: [A])
        <> con "c" True
        <> con "d" 'x'
        <> con "e" (0 :: Int)

atom :: Text -> TypeSkeleton -> Term
atom name ty = Term (Symbol name) [typeSkeletonToTerm ty]

-- The public validator checks each application before comparison.
application :: Term -> Term -> Either String Term
application fun arg = do
    funType <- termType signature fun
    argType <- termType signature arg
    case funType of
        TFun expected result | expected == argType -> do
            let term = Term "app" [typeSkeletonToTerm result, fun, arg]
            _ <- termType signature term
            pure term
        _ -> Left "invalid application in comparator regression"

example :: TypeSkeleton -> TypeSkeleton -> Text -> Either String Term
example first second name = do
    let int = typeSkeletonOf (Proxy :: Proxy Int)
        fun = atom "f" (TFun first (TFun second int))
    prefix <- application fun (atom "[]" first)
    application prefix (atom name second)

main :: IO ()
main = do
    let examples = sequence
            [ example (typeSkeletonOf (Proxy :: Proxy [A])) (typeSkeletonOf (Proxy :: Proxy Bool)) "c"
            , example (typeSkeletonOf (Proxy :: Proxy [B])) (typeSkeletonOf (Proxy :: Proxy Char)) "d"
            , example (typeSkeletonOf (Proxy :: Proxy [A])) (typeSkeletonOf (Proxy :: Proxy Int)) "e"
            ]
    case examples of
        Left problem -> fail problem
        Right [s, t, u] -> do
            let int = typeSkeletonOf (Proxy :: Proxy Int)
                order = termCompare (PathOrder ["e", "c", "f"]) (const False)
                comparisons xs = zipWith order xs (drop 1 xs ++ take 1 xs)
                raw = comparisons [s, t, u]
                canonical = comparisons (map canonicalTypes [s, t, u])
            unless (all ((== Right int) . termType signature) [s, t, u]) $
                fail "the terms do not share the validated Int result type"
            putStrLn "Validated Int terms: f ([] :: [A]) (c :: Bool), f ([] :: [B]) (d :: Char), f ([] :: [A]) (e :: Int)"
            putStrLn ("s/t, t/u, u/s: " ++ show raw)
            putStrLn ("after canonicalTypes: " ++ show canonical)
            let transitive xs = and
                    [ not (order a b == LT && order b c == LT) || order a c == LT
                    | a <- xs, b <- xs, c <- xs
                    ]
                opposite LT = GT
                opposite EQ = EQ
                opposite GT = LT
                antisymmetric xs = and [order a b == opposite (order b a) | a <- xs, b <- xs]
            unless (all transitive [[s,t,u],map canonicalTypes [s,t,u]]
                    && all antisymmetric [[s,t,u],map canonicalTypes [s,t,u]]) $
                fail "the repaired comparator fails on the recorded terms"
            putStrLn "PASS: recorded annotated terms have transitive and antisymmetric comparisons"
        Right _ -> fail "unexpected example count"
