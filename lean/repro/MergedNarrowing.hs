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
unionLoop s = Mu (\self -> Node [Edge s [], Edge "f" [createUnion [self, leaf "c"]]]) :: Node String

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
    let source = case args of
            ["union"] -> union [createUnion [unionLoop "a", leaf "c"], createUnion [unionLoop "b", leaf "c"]]
            _ -> union [loop "a", loop "b"]
        merged = mergeAlternatives source
        terms = [iterate (T.One "f") (T.Leaf s) !! n | s <- ["a", "b", "c"], n <- [0 .. 8]]
        classes = E.mkEqConstraints [[E.path [0], E.path [1]]]
        reduced = E.reduceEqConstraints classes E.EmptyConstraints [source, source]
        raw =
            Node [mkEdge "raw" [] (semanticConstraint (Not Top)), mkEdge "raw" [] (semanticConstraint (Not (Or [Top])))] ::
                Node String
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
    check "merged root completed" (length (nodeEdges merged) <= 4)
    check "sampled language preserved" (all (\t -> E.accepts source t == E.accepts merged t) terms)
    check "parent reduction completed" (length (concatMap nodeEdges reduced) <= 2 * length (nodeEdges source))
    check "parent sampled language preserved" (all (\t -> all (\n -> E.accepts n t == E.accepts source t) reduced) terms)
    check "nullary guard widening" (not (accepts raw (T.Leaf "raw")) && accepts (mergeAlternatives raw) (T.Leaf "raw"))
