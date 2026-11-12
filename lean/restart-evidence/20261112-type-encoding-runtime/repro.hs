{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.CFTA.Constraint (equalitiesHold, residual)
import Data.CFTA.Equality (acceptsWith)
import Data.CFTA.Gen.Synthesis
import Data.CFTA.Symbol (Symbol)
import qualified Data.CFTA.Term as Term
import System.Timeout (timeout)

-- | Build the literal application and filter for f : a -> B and x.
candidate :: Symbol -> Term.Term Symbol
candidate argumentSymbol = Term.Node "filter" [result, application]
  where
    marker = Term.Node "(->)" []
    result = Term.Node "B" []
    function = Term.Node "f" [Term.Node "->" [marker, Term.Node "var1" [], result]]
    argument = Term.Node "x" [Term.Node argumentSymbol []]
    application = Term.Node "app" [result, marker, function, argument]

-- | Check the raw language and the actual reduced program output.
probe :: Library -> String -> Type -> Symbol -> IO ()
probe lib label argumentType argumentSymbol = do
    let result = TCons "B" []
        query = Query [("f", TFun (TVar "a") result), ("x", argumentType)] result
        accepted =
            acceptsWith
                (\constraint term -> not (residual constraint) && equalitiesHold constraint term)
                (rawSearchSpace lib query 2)
                (candidate argumentSymbol)
        output = show (accepted, solutionsOfSize lib query 2)
    observed <- timeout 10000000 $ do
        _ <- evaluate (length output)
        pure output
    print (label, observed)

-- | Distinct query TVars test rigid lookup, rather than component specialization.
main :: IO ()
main = do
    let lib = (library [] [] []){libraryEncoding = FirstOrder}
    print ("raw-types-equal", TVar "a" == TCons "var1" [])
    print ("encoded-type-nodes-equal", typeNode (TVar "a") == typeNode (TCons "var1" []))
    forM_
        [ ("same rigid TVar", TVar "a", "var1")
        , ("different rigid TVar", TVar "b", "var2")
        , ("reserved constant", TCons "var1" [], "var1")
        , ("ordinary constant", TCons "A" [], "A")
        ]
        (\(label, typ, symbol) -> probe lib label typ symbol)
