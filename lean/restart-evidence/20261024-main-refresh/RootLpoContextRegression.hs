{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Monad (unless)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Specftacular.Rewriting (TermOrder (PathOrder), termCompare)
import Specftacular.Types

signature :: Sig
signature =
    con "f" ((\g -> g) :: (A -> A) -> A -> A)
        <> con "a" (id :: A -> A)
        <> con "x" (A 0)

atom :: Text -> TypeSkeleton -> Term
atom name ty = Term (Symbol name) [typeSkeletonToTerm ty]

application :: Term -> Term -> Either String Term
application fun arg = do
    funType <- termType signature fun
    argType <- termType signature arg
    case funType of
        TFun expected result | expected == argType -> do
            let term = Term "app" [typeSkeletonToTerm result, fun, arg]
            _ <- termType signature term
            pure term
        _ -> Left "invalid application in context regression"

main :: IO ()
main = do
    let carrier = typeSkeletonOf (Proxy :: Proxy A)
        endo = TFun carrier carrier
        f = atom "f" (TFun endo endo)
        a = atom "a" endo
        x = atom "x" carrier
        terms = do
            fa <- application f a
            fax <- application fa x
            ax <- application a x
            pure (fa, fax, ax)
    case terms of
        Left problem -> fail problem
        Right (fa, fax, ax) -> do
            let order = termCompare (PathOrder ["f", "a"]) (const False)
                before = order fa a
                inside = order fax ax
            unless (termType signature fa == Right endo && termType signature a == Right endo
                    && termType signature fax == Right carrier && termType signature ax == Right carrier) $
                fail "the terms do not have the required validated types"
            putStrLn ("compare (f a) a: " ++ show before)
            putStrLn ("compare ((f a) x) (a x): " ++ show inside)
            unless (before == GT && inside == LT) $
                fail "the reported application-context reversal was not reproduced"
