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
                comparisons xs = zipWith order xs (tail xs ++ take 1 xs)
                raw = comparisons [s, t, u]
                canonical = comparisons (map canonicalTypes [s, t, u])
            unless (all ((== Right int) . termType signature) [s, t, u]) $
                fail "the terms do not share the validated Int result type"
            putStrLn "Validated Int terms: f ([] :: [A]) (c :: Bool), f ([] :: [B]) (d :: Char), f ([] :: [A]) (e :: Int)"
            print ("s/t, t/u, u/s", raw)
            print ("after canonicalTypes", canonical)
            unless (raw == [LT, LT, LT] && canonical == [LT, LT, LT]) $
                fail "the reported upstream comparator cycle was not reproduced"
        Right _ -> fail "unexpected example count"
