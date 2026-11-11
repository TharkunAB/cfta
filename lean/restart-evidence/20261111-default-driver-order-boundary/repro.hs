{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.CFTA.Equality (
    Edge (Edge),
    Node (Node),
    PartialSymbol (..),
    noExpansionPreference,
    runsBy,
    termsPruneUntil,
 )
import Data.CFTA.Symbol (Symbol)
import qualified Data.CFTA.Term as Term
import Data.List (sort)

-- | A finite ordinary grammar with two independent choices.
grammar :: Node Symbol
grammar =
    Node
        [ Edge
            "r"
            [ Node [Edge "f" [Node [Edge "a" [], Edge "b" []]]]
            , Node [Edge "c" [], Edge "d" []]
            ]
        ]

-- | Build one expected concrete term.
resultTerm :: Symbol -> Symbol -> Term.Term Symbol
resultTerm first second =
    Term.Node "r" [Term.Node "f" [Term.Node first []], Term.Node second []]

-- | Reject unresolved symbols during conversion to the concrete alphabet.
concrete :: PartialSymbol Symbol -> Maybe Symbol
concrete (ConcreteSymbol symbol) = Just symbol
concrete _ = Nothing

-- | Print both public observations and the source-derived predictions.
main :: IO ()
main = do
    let eagerRuns = runsBy (const 0) "Mu" grammar
        eager = map fst eagerRuns
        shallowRaw =
            termsPruneUntil
                ()
                noExpansionPreference
                (\_ _ node -> node)
                (\_ _ -> False)
                (\state _ _ -> pure (False, state))
                grammar
        shallow = traverse (traverse concrete) shallowRaw
        expectedEager = [resultTerm first second | first <- ["a", "b"], second <- ["c", "d"]]
        expectedShallow = [resultTerm first second | second <- ["c", "d"], first <- ["a", "b"]]
    putStrLn ("eager=" ++ show eager)
    putStrLn ("shallow_raw=" ++ show shallowRaw)
    putStrLn ("shallow_concrete=" ++ show shallow)
    print ("eager_matches_prediction", eager == expectedEager)
    print ("shallow_matches_prediction", shallow == Just expectedShallow)
    print ("same_order", shallow == Just eager)
    print ("same_multiset", fmap sort shallow == Just (sort eager))
    print ("eager_residuals_empty", all (null . snd) eagerRuns)
    print ("counts", length eager, length <$> shallow)
