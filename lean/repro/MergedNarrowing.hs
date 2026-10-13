{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import qualified Data.CFTA.Equality as E
import Data.CFTA.Interned
import Data.CFTA.Interned.Operations (mergeAlternatives)
import qualified Data.CFTA.Term as T
import System.Environment (getArgs)
import System.IO (BufferMode (..), hSetBuffering, stdout)
import System.Timeout (timeout)

-- | Construct one unconstrained leaf.
leaf :: String -> Node String
leaf s = Node [Edge s []] :: Node String

-- | Accept a finite chain of f constructors ending at the given leaf.
loop :: String -> Node String
loop s = Mu (\self -> Node [Edge s [], Edge "f" [self]]) :: Node String

-- | Retain a recursive union in the recursive child.
unionLoop :: String -> Node String
unionLoop s = Mu (\self -> Node [Edge s [], Edge "f" [createUnion [self, leaf "extra"]]]) :: Node String

-- | Force the check with a bounded wait.
check :: String -> Bool -> IO ()
check label action = do
    result <- timeout 3000000 (evaluate action)
    putStrLn (label ++ ": " ++ show result)
    unless (result == Just True) (fail label)

-- | Replay the direct case, or the wrapped-union case with the union argument.
main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    args <- getArgs
    let names = ["a", "b", "c", "d", "e"]
        source = case args of
            ["union"] -> union [createUnion [unionLoop name, leaf "extra"] | name <- names]
            _ -> union (map loop names)
        merged = mergeAlternatives source
        terms = [iterate (T.One "f") (T.Leaf s) !! n | s <- "extra" : names, n <- [0 .. 8]]
        classes = E.mkEqConstraints [[E.path [0], E.path [1]]]
        reduced = E.reduceEqConstraints classes E.EmptyConstraints [source, source]
        guards = [Not (Or (replicate count Top)) | count <- [1 .. 5]]
        rawEdges = [mkEdge "raw" [] (semanticConstraint guard) | guard <- guards]
        rawFour = Node (take 4 rawEdges) :: Node String
        rawFive = Node rawEdges :: Node String
        duplicated = Node (take 4 rawEdges ++ take 4 rawEdges) :: Node String
        wrapped = Node [Edge "wrap" [rawFive]]
        wrappedTerm = T.One "wrap" (T.Leaf "raw")
        recursiveEdges :: Node String -> [Edge String]
        recursiveEdges node = [edge | edge <- nodeEdges node, edgeSymbol edge == "f", length (edgeChildren edge) == 1]
        eval :: Guard -> Bool
        eval Top = True
        eval Bottom = False
        eval (Not p) = not (eval p)
        eval (And ps) = all eval ps
        eval (Or ps) = any eval ps
        eval _ = error "unexpected guard"
        accepts :: Node String -> T.Term String -> Bool
        accepts = acceptsWith (\constraint _ -> eval (constraintGuard constraint))
    putStrLn ("input edges: " ++ show (length (nodeEdges source)))
    check "five recursive alternatives enter merge branch" (length (recursiveEdges source) == 5)
    check "merged root completed" (length (recursiveEdges merged) == 1)
    check "sampled language preserved" (all (\t -> E.accepts source t == E.accepts merged t) terms)
    check "parent reduction completed" (length (concatMap nodeEdges reduced) <= 2 * length (nodeEdges source))
    check "parent sampled language preserved" (all (\t -> all (\n -> E.accepts n t == E.accepts source t) reduced) terms)
    check "four distinct raw guards stay exact" (length (nodeEdges rawFour) == 4 && mergeAlternatives rawFour == rawFour)
    check "duplicate rows do not trigger merge" (duplicated == rawFour && mergeAlternatives duplicated == rawFour)
    check
        "five distinct raw guards merge"
        (length (nodeEdges rawFive) == 5 && length (nodeEdges (mergeAlternatives rawFive)) == 1)
    check "small rejecting group stays rejecting" (not (accepts (mergeAlternatives rawFour) (T.Leaf "raw")))
    check
        "large nullary guard widening"
        (not (accepts rawFive (T.Leaf "raw")) && accepts (mergeAlternatives rawFive) (T.Leaf "raw"))
    check
        "small parent visits large child"
        (not (accepts wrapped wrappedTerm) && accepts (mergeAlternatives wrapped) wrappedTerm)
