{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Data.CFTA.Enumeration (runsInterned)
import Data.CFTA.Equality
import qualified Data.Set as Set
import System.Timeout (timeout)

{- | Separate closed input construction from default enumeration.
A timeout does not prove nontermination.
-}
main :: IO ()
main = do
    let same = equalityConstraint (mkEqConstraints [[path [0], path [1]], [path [0, 0], path [1, 0]]])
        p x = Node [mkEdge "p" [x, x] same]
        a = Mu $ \x -> Node [Edge "a" [], mkEdge "p" [x, x] same, mkEdge "p" [p x, p x] same]
        b = Mu $ \x -> Node [Edge "a" [], mkEdge "p" [x, a] same]
        root :: Node String
        root = Node [mkEdge "p" [b, a] same]
    prepared <-
        timeout
            5000000
            (evaluate (let n = nodeCount root; e = edgeCount root; c = Set.null (freeVars root) in n `seq` e `seq` c `seq` (n, e, c)))
    print ("construction", prepared)
    case prepared of
        Nothing -> pure ()
        Just _ -> do
            result <- timeout 8000000 (evaluate (length (take 1 (runsInterned "Mu" root))))
            print ("enumeration", result)
