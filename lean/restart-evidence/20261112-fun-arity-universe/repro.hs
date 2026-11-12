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

-- | Build the literal application with the given result annotation.
candidate :: Term.Term Symbol -> Term.Term Symbol
candidate result = Term.Node "filter" [result, application]
  where
    marker = Term.Node "(->)" []
    argument = Term.Node "A" []
    function = Term.Node "f" [Term.Node "->" [marker, argument, result]]
    value = Term.Node "x" [argument]
    application = Term.Node "app" [result, marker, function, value]

-- | Compare raw acceptance with the actual reduced program output.
probe :: Library -> String -> Type -> Term.Term Symbol -> IO ()
probe lib label result term = do
    let argument = TCons "A" []
        query = Query [("f", TFun argument result), ("x", argument)] result
        accepted =
            acceptsWith
                (\c t -> not (residual c) && equalitiesHold c t)
                (rawSearchSpace lib query 2)
                (candidate term)
        output = show (accepted, solutionsOfSize lib query 2)
    observed <- timeout 10000000 $ evaluate (length output) >> pure output
    print (label, observed)

-- | Test ordinary constructors, both non-arrow Fun arities, and the Fun/2 alias.
main :: IO ()
main = do
    let lib = (library [] [] []){libraryEncoding = FirstOrder}
        a = TCons "A" []
        leaf = Term.Node "A" []
    print ("parsed Fun/0", parseType "Fun")
    print ("parsed Fun/3", parseType "Fun A A A")
    forM_
        [ ("ordinary result", TCons "Z" [], Term.Node "Z" [])
        , ("Fun/0 result", TCons "Fun" [], Term.Node "Fun" [])
        , ("Fun/3 result", TCons "Fun" [a, a, a], Term.Node "Fun" [leaf, leaf, leaf])
        , ("Fun/2 alias result", TCons "Fun" [a, a], Term.Node "->" [Term.Node "(->)" [], leaf, leaf])
        ]
        (\(label, typ, term) -> probe lib label typ term)
    let result = TCons "Fun" []
    print ("rigid Fun/0 leaf", solutionsOfSize lib (Query [("x", result)] result) 1)
