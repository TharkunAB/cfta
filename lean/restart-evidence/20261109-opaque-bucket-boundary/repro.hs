{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import qualified Data.CFTA.Equality as E
import Data.CFTA.Symbol (Symbol)
import qualified Data.CFTA.Term as T

-- | Build one unconstrained nullary alternative.
leaf :: Symbol -> E.Node Symbol
leaf symbol = E.Node [E.Edge symbol []]

-- | Compare actual public enumeration with membership and an exposed control.
main :: IO ()
main = do
    let a = leaf "a"
        recursive = E.createMu (\self -> E.Node [E.Edge "a" [], E.Edge "p" [self]])
        opaque = E.createUnion [leaf "b", recursive]
        constraint = E.equalityConstraint (E.mkEqConstraints [[E.path [0, 0], E.path [1]]])
        parent child = E.Node [E.mkEdge "r" [child, a] constraint]
        original = parent opaque
        exposed = parent (E.Node (E.nodeEdges opaque))
        bad = T.Node "r" [T.Node "b" [], T.Node "a" []]
        good = T.Node "r" [T.Node "p" [T.Node "a" []], T.Node "a" []]
        keep () _ _ = pure (False, ())
        actual = take 12 (E.termsPrune () keep original)
        control = take 12 (E.termsPrune () keep exposed)
        isOpaque = case opaque of
            E.InternedUnion _ -> True
            _ -> False
    print ("real InternedUnion", isOpaque)
    print ("closed opaque", null (E.freeVars opaque))
    print ("parent survives mkEdge", original /= E.EmptyNode)
    print ("bad parent paths", map (`E.getPath` bad) [E.path [0, 0], E.path [1]])
    print ("bad satisfies parent equality", E.equalitiesHold constraint bad)
    print ("bad accepted", E.accepts original bad)
    print ("good accepted", E.accepts original good)
    print ("actual termsPrune, first 12", actual)
    print ("bad concrete term emitted in prefix", bad `elem` actual)
    print ("recognition of returned terms including markers", [(term, E.accepts original term) | term <- actual])
    print ("explicit truncation, first 12", take 12 (E.truncatedTerms original))
    print ("one-layer exposed child control, first 12", control)
