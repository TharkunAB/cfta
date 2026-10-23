{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

-- Run this probe in the cfta package environment. This file is not a committed test.
module Main (main) where

import Control.Monad (unless)
import Data.CFTA.Equality
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import Data.List (sort)

-- Check both the values and their occurrence counts. Enumeration order is not checked.
assertSame :: (Ord a, Show a) => String -> [a] -> [a] -> IO ()
assertSame label expected actual = do
    unless (sort expected == sort actual) $
        ioError (userError (label <> ": expected " <> show expected <> ", got " <> show actual))
    putStrLn ("PASS " <> label)

-- Retain every branch and the caller state.
keepEverything :: a -> UVar -> Either (TermFragment Symbol) (Node Symbol) -> EnumerateM Symbol (Bool, a)
keepEverything state _ _ = pure (False, state)

-- Expand every eligible hole without changing its node.
noStop :: Node Symbol -> [Term (PartialSymbol Symbol)]
noStop = termsPruneUntil () noExpansionPreference (\_ _ node -> node) (\_ _ -> False) keepEverything

-- Remove only alternatives whose symbol is b. The probe uses finite ordinary nodes.
narrowToA :: () -> UVar -> Node Symbol -> Node Symbol
narrowToA _ _ node = Node [edge | edge <- nodeEdges node, edgeSymbol edge /= "b"]

-- Select the program child before the annotation child in the finite probe.
preferLast :: ExpansionOrder (Maybe UVar)
preferLast _ candidates = case reverse candidates of
    uv : _ -> Just uv
    [] -> Nothing

-- Record the annotation hole from the actual fragment returned for the root.
markAnnotation :: Maybe UVar -> UVar -> Either (TermFragment Symbol) (Node Symbol) -> EnumerateM Symbol (Bool, Maybe UVar)
markAnnotation _ _ (Left (TermFragmentNode symbol [TermFragmentUVar annotation, _]))
    | symbol == "typed" = pure (False, Just annotation)
markAnnotation state _ _ = pure (False, state)

main :: IO ()
main = do
    let choices = Node [Edge "a" [], Edge "b" []] :: Node Symbol
        pairs = Node [Edge "g" [choices, choices]]
        partial = fmap ConcreteSymbol
    assertSame "no-stop identity preserves this full finite language" (map partial (terms pairs)) (noStop pairs)
    assertSame "no-stop EmptyNode has no terms" [] (noStop (EmptyNode :: Node Symbol))

    -- Stop runs before the empty-node test. This hole has no concrete completion.
    let stoppedEmpty = termsPruneUntil () noExpansionPreference (\_ _ node -> node) (\_ _ -> True) keepEverything (EmptyNode :: Node Symbol)
    assertSame "stop=true can return a speculative EmptyNode hole" [Term.Node (UVarHole (intToUVar 0)) []] stoppedEmpty

    let narrowed = termsPruneUntil () noExpansionPreference narrowToA (\_ _ -> False) keepEverything pairs
        onlyA = Term.Node (ConcreteSymbol "g") [Term.Node (ConcreteSymbol "a") [], Term.Node (ConcreteSymbol "a") []]
    assertSame "actual child narrowing removes b alternatives" [onlyA] narrowed

    let annotations = Node [Edge "T" []] :: Node Symbol
        programs = Node [Edge "p" [], Edge "q" []] :: Node Symbol
        annotated = Node [Edge "typed" [annotations, programs]]
        stoppedAnnotations = termsPruneUntil Nothing preferLast (\_ _ node -> node) (\annotation uv -> annotation == Just uv) markAnnotation annotated
        expectedAnnotated symbol = Term.Node (ConcreteSymbol "typed") [Term.Node (UVarHole (intToUVar 1)) [], Term.Node (ConcreteSymbol symbol) []]
    assertSame "stop with only the annotation hole remaining" (map expectedAnnotated ["p", "q"]) stoppedAnnotations

    -- Each exclusion has its own prepared-template catalog. Both catalogs reuse IDs.
    let excludeA = exclude [TemplateNode "a" []] :: Node Symbol -> Node Symbol
        excludeB = exclude [TemplateNode "b" []] :: Node Symbol -> Node Symbol
        other = Node [Edge "a" [], Edge "c" []] :: Node Symbol
    assertSame "first exclusion catalog" [Term.Node "b" []] (terms (excludeA choices))
    assertSame "second exclusion catalog stays separate" [Term.Node "a" []] (terms (excludeB choices))
    assertSame "first catalog still works after the second" [Term.Node "b" []] (terms (excludeA choices))
    assertSame "one exclusion closure accepts another input node" [Term.Node "c" []] (terms (excludeA other))
