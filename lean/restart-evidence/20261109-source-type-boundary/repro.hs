{-# LANGUAGE OverloadedStrings #-}

import Control.Monad (forM_)
import qualified Data.Map.Strict as Map

import qualified Data.CFTA.Equality as E
import qualified Data.CFTA.Gen.Equality as Gen
import Data.CFTA.Gen.Synthesis
import Data.CFTA.Symbol (Symbol)
import qualified Data.CFTA.Term as Term

-- This fixture separates the raw source from the public reduced search.
-- The expected program is f x. The finite witness gives f the type A -> B.
main :: IO ()
main = forM_ encodings $ \encoding -> do
    let lib = Library [("f", TVar "a", ["f"])] [] [] encoding
        query = Query [("x", TCons "A" [])] (TCons "B" [])
        raw = rawSearchSpace lib query 2
        rawSpace = Space raw (const 0)
        reduced = reduceWithOrder raw
        generated = programsOfSize lib query 2
    putStrLn ("encoding: " <> show encoding)
    putStrLn ("raw accepts finite witness: " <> show (E.accepts raw witness))
    putStrLn ("raw typed runs: " <> show (take 4 (E.runsBy (const 0) "Mu" raw)))
    putStrLn ("raw partial terms: " <> show (take 4 (E.truncatedTerms raw)))
    putStrLn ("raw programRuns: " <> show (take 4 (programRuns encoding rawSpace)))
    putStrLn ("reduced typed runs: " <> show (take 4 (E.runsBy (spaceOrder reduced) "Mu" (spaceNode reduced))))
    putStrLn ("reduced programRuns: " <> show (take 4 (programRuns encoding reduced)))
    putStrLn ("solutionsOfSize: " <> show (take 4 (solutionsOfSize lib query 2)))
    putStrLn ("generator cardinality: " <> show (Gen.cardinality generated))
    putStrLn ("generator values: " <> show (Gen.values generated))
  where
    encodings = [FirstOrder, Curried AnyHead Map.empty, Curried OnlyDefault Map.empty]

witness :: Term.Term Symbol
witness =
    Term.Node
        "filter"
        [ b
        , Term.Node
            "app"
            [ b
            , marker
            , Term.Node "f" [Term.Node "->" [marker, a, b]]
            , Term.Node "x" [a]
            ]
        ]
  where
    a = Term.Node "A" []
    b = Term.Node "B" []
    marker = Term.Node "(->)" []
