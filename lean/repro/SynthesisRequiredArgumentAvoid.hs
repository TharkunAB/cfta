{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Data.CFTA.Gen.Synthesis
import System.Timeout (timeout)

-- | Compare the documented head ban with and without a required argument.
main :: IO ()
main = do
    let int = TCons "Int" []
        f = ("f", TFun int int)
        banned = [(["f"], Nothing)]
        required = library [f] [] banned
        componentArgument = library [f, ("x", int)] [] banned
        unrestricted = library [f] [] []
        query = Query [("x", int)] int
        noRequired = Query [] int
        found lib q = evaluate (App (Var "f") (Var "x") `elem` concatMap (expand lib) (solutionsOfSize lib q 2))
    a <- timeout 10000000 (found required query)
    b <- timeout 10000000 (found componentArgument noRequired)
    c <- timeout 10000000 (found unrestricted query)
    print ("required-argument-with-ban", a)
    print ("component-argument-with-ban", b)
    print ("required-argument-without-ban", c)
