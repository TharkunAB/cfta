{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Equality
import Data.CFTA.Enumeration (unconstrained)
import qualified Data.Set as Set
import System.IO (BufferMode(LineBuffering), hSetBuffering, stdout)
import System.Timeout (timeout)

step :: Node String -> Node String
step child = Node [Edge "f" [child]]

height :: Node String -> Int
height EmptyNode = 0
height (Mu _) = 0
height (InternedUnion _) = 0
height (Rec _) = 0
height (Node edges) = 1 + maximum (0 : map height (concatMap edgeChildren edges))

children :: Node String -> [Node String]
children value = case nodeEdges value of
    [edge] -> edgeChildren edge
    _ -> []

sameTerms :: Node String -> Node String -> Bool
sameTerms before after = and
    [Set.fromList (terms (boundDepth depth before)) == Set.fromList (terms (boundDepth depth after)) | depth <- [0..5]]

check :: String -> Bool -> IO ()
check label value = do
    answer <- timeout 10000000 (evaluate value)
    print (label, answer)
    unless (answer == Just True) (fail label)

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    let chain = Mu (\self -> Node [Edge "a" [], Edge "f" [self]]) :: Node String
        evenChain = Mu (\self -> Node [Edge "a" [], Edge "f" [step self]])
        direct = mkEqConstraints [[path [0], path [1]]]
        directRoot = Node [mkEdge "pair" [chain, evenChain] (equalityConstraint direct)]
        directResult = reducePartially directRoot
    check "selected distinct recursive endpoints really narrow"
        (chain /= evenChain && unconstrained chain && unconstrained evenChain
        && not (unconstrained directRoot) && Set.null (freeVars directRoot)
        && length (children directResult) == 2
        && head (children directResult) /= chain
        && head (children directResult) == last (children directResult)
        && nodeCount directResult + edgeCount directResult > 0
        && sameTerms directRoot directResult)
    let unequal = mkEqConstraints [[path [0,0,0], path [1,0]]]
        unequalRoot = Node [mkEdge "pair" [chain, chain] (equalityConstraint unequal)]
        unequalResult = reducePartially unequalRoot
        expectedChildren = [step (step chain), step chain]
    check "unequal selected paths unfold unconstrained recursive inputs"
        (children unequalResult == expectedChildren
        && getPath (path [0,0,0]) (children unequalResult) == chain
        && getPath (path [1,0]) (children unequalResult) == chain
        && sameTerms unequalRoot unequalResult
        && reducePartially unequalResult == unequalResult)
    print ("ordinary heights original/result/returned children", height unequalRoot, height unequalResult, map height (children unequalResult))
    let productNode = intersect chain (step chain)
    check "min ordinary-height bound fails outside finite ordinary domain"
        (height chain == 0 && height (step chain) == 1 && height productNode == 1
        && productNode == step chain && unconstrained productNode)
    let own = mkEqConstraints [[path [0], path [1,0,0]], [path [0,1], path [1,0,1]]]
        next inherited = eqConstraintsDescend (combineEqConstraints inherited own) 1
        maxLength constraints = maximum (0 : [length (unPath p) | ec <- unsafeGetEclasses constraints, p <- Set.toList (unPathEClass ec)])
        lengths = map maxLength (take 8 (iterate next EmptyConstraints))
    check "fixed own payload does not bound inherited path depth" (lengths == [0,3,4,5,6,7,8,9])
    print ("inherited maximum path lengths", lengths)
