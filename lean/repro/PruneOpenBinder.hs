{-# LANGUAGE OverloadedStrings #-}

-- | Check pruning through an open nested binder with an enclosing union reference.
module Main (main) where

import Data.CFTA.Interned (createMu, createUnion)
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true)
import qualified Data.CFTA.Term as Term

-- | The observed first child is a fixed leaf even when its parent is recursive.
main :: IO ()
main = do
    let leaf = Node [Transition "a" true [] noConstraint]
        grammar = createMu $ \outer ->
            Node
                [ Transition "base" true [] noConstraint
                , Transition
                    "outer"
                    true
                    [ leaf
                    , createMu $ \inner ->
                        createUnion
                            [ outer
                            , Node [Transition "inner" true [leaf, inner] noConstraint]
                            ]
                    ]
                    (semanticConstraint $ Satisfies (path [1, 0]) true)
                ]
        solver = Entailment $ \_ _ -> pure Yes
        wanted =
            Term.Node
                (RefinedSymbol "outer" true)
                [ Term.Node (RefinedSymbol "a" true) []
                , Term.Node
                    (RefinedSymbol "inner" true)
                    [Term.Node (RefinedSymbol "a" true) [], Term.Node (RefinedSymbol "base" true) []]
                ]
    print $ validate grammar
    print =<< accepts solver grammar wanted
    pruned <- prune solver grammar
    case pruned of
        Left err -> error $ show err
        Right result -> do
            verdict <- accepts solver result wanted
            print verdict
            if verdict == Yes then pure () else error "Pruning lost the valid nested-binder term."
