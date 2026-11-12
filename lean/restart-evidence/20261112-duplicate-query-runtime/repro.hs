{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.CFTA.Constraint (equalitiesHold, residual)
import Data.CFTA.Equality (acceptsWith)
import Data.CFTA.Gen.Synthesis
import Data.CFTA.Symbol (Symbol)
import qualified Data.CFTA.Term as Term
import Data.Text (Text)
import System.Timeout (timeout)

-- | Build g applied to one A input and two C inputs with exact annotations.
candidate :: Symbol -> Symbol -> Term.Term Symbol
candidate firstName laterName = Term.Node "filter" [r, application]
  where
    a = Term.Node "A" []
    c = Term.Node "C" []
    r = Term.Node "R" []
    marker = Term.Node "(->)" []
    arrow domain codomain = Term.Node "->" [marker, domain, codomain]
    apply result function argument = Term.Node "app" [result, marker, function, argument]
    function = Term.Node "g" [arrow a (arrow c (arrow c r))]
    first = apply (arrow c (arrow c r)) function (Term.Node firstName [a])
    second = apply (arrow c r) first (Term.Node laterName [c])
    application = apply r second (Term.Node laterName [c])

-- | Observe raw acceptance and the actual reduced output at four components.
probe :: String -> [(Text, Type)] -> Symbol -> Symbol -> IO ()
probe label arguments firstName laterName = do
    let a = TCons "A" []
        c = TCons "C" []
        r = TCons "R" []
        lib = Library [("g", TFun a (TFun c (TFun c r)), ["g"])] [] [] FirstOrder
        query = Query arguments r
        accepted =
            acceptsWith
                (\constraint term -> not (residual constraint) && equalitiesHold constraint term)
                (rawSearchSpace lib query 4)
                (candidate firstName laterName)
        output = show (accepted, solutionsOfSize lib query 4)
    observed <- timeout 10000000 $ do
        _ <- evaluate (length output)
        pure output
    print (label, observed)

-- | Compare mixed duplicate bindings with last-only, coherent, and distinct names.
main :: IO ()
main = do
    let a = TCons "A" []
        c = TCons "C" []
    forM_
        [ ("mixed duplicate A,C", [("x", a), ("x", c)], "x", "x")
        , ("only last C", [("x", c)], "x", "x")
        , ("coherent duplicate C,C", [("x", c), ("x", c)], "x", "x")
        , ("mixed reversed C,A", [("x", c), ("x", a)], "x", "x")
        , ("distinct names", [("a", a), ("c", c)], "a", "c")
        ]
        (\(label, arguments, firstName, laterName) -> probe label arguments firstName laterName)
