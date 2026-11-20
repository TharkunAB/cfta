{-# LANGUAGE OverloadedStrings #-}

{- | Build a tower of languages and check that it keeps the meaning of old terms.

The base language has two digits and sums. One definitional extension adds the
constructor @double@. The program shows four steps: the terms of each level,
the meaning of the terms of the base, the refusal of a bad extension with the
term that changes meaning, and the facts of the base that stay in the top
language.
-}
module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Index (Size (..))
import Data.CFTA.Language (Language (..))
import qualified Data.CFTA.Language as L
import qualified Data.CFTA.Language.Source as D
import Data.CFTA.Lowering (Expansion (..))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Sized (sized, termsOfSize)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Exclusion (..), Template (..))
import Data.CFTA.Term (Term (Node))
import Data.CFTA.Tower

-- | The base language: two digits and sums, with a fact on a digit and on the sum, and an exclusion.
base :: Language String
base =
    Language
        ( either (error . show) id $
            D.mkDocument
                "e"
                [
                    ( "e"
                    ,
                        [ production "zero" "zero" [] [("digit", noConstraint)]
                        , production "one" "one" [] []
                        , production "add" "add" ["e", "e"] [("sum", noConstraint)]
                        ]
                    )
                ]
        )
        (Map.singleton "never" $ AtRoot $ TemplateNode "unused" [])
  where
    production name symbol children facts = FTA.Transition symbol children $ D.Annotation name $ Map.fromList facts

-- | The extension that adds @double(x)@ as @add(x, x)@.
doubling :: Extension String
doubling = Definitional [Definition "e" "double" "double" ["e"] (Apply "add" [Child 0, Child 0])]

-- | A bad extension: it gives the old constructor @add@ another expansion.
badSum :: Extension String
badSum = Definitional [Definition "e" "add2" "add" ["e", "e"] (Apply "add" [Child 0, Child 0])]

-- | The terms of a language with a size, as the example counts them.
termsOfSizeIn :: Language String -> Int -> [Term Symbol]
termsOfSizeIn language size = case sized (D.compileGraph $ L.source language) of
    Right classes -> termsOfSize classes (Size $ toInteger size)
    Left _ -> []

-- | The names of the facts of each production of a language, by the name of the production.
factsOf :: Language String -> Map.Map D.ProductionName [D.FactName]
factsOf language =
    Map.fromList
        [ (D.annotationName a, Map.keys $ D.annotationFacts a)
        | a <- map FTA.transitionConstraint $ concat $ Map.elems $ FTA.transitionTable $ D.sourceGraph $ L.source language
        ]

-- | Run the four steps. Each step checks what it prints.
main :: IO ()
main = withZ3 [] $ \z3 -> do
    putStrLn "step 1: expand the base with double"
    expanded <- expand z3 0 doubling (tower (Size 5) base) >>= either (fail . show) pure
    putStrLn $ "version: " <> show (version expanded)
    unless (version expanded == 1) $ fail "wrong version"
    let top = current expanded
    let counts language = [length $ termsOfSizeIn language size | size <- [1 .. 5]]
    putStrLn $ "terms of the base, by size: " <> show (counts base)
    putStrLn $ "terms of level 1, by size: " <> show (counts top)
    unless (counts base == [2, 0, 4, 0, 16]) $ fail "wrong count of the base"
    unless (counts top == [2, 2, 6, 14, 42]) $ fail "wrong count of level 1"

    putStrLn "step 2: the terms of the base keep their meaning"
    let reports = keptMeaning expanded
    forM_ reports $ \report ->
        putStrLn $
            "level "
                <> show (reportLevel report)
                <> ": checked "
                <> show (reportChecked report)
                <> ", changes "
                <> show (length $ reportChanges report)
    unless (map reportChecked reports == [22] && all (null . reportChanges) reports) $ fail "a term changed meaning"
    forM_ (concatMap (termsOfSizeIn base) [1 .. 5]) $ \term ->
        unless (meaning expanded 1 term == meaning expanded 0 term) $ fail $ "meaning changed for " <> show term
    putStrLn "meaning at level 1 equals meaning at level 0 for all 22 terms"
    putStrLn $ "meaning of double(zero): " <> show (meaning expanded 1 (Node "double" [Node "zero" []]))
    unless (meaning expanded 1 (Node "double" [Node "zero" []]) == Just (Node "add" [Node "zero" [], Node "zero" []])) $
        fail "wrong meaning of double"

    putStrLn "step 3: a bad extension is refused with a term"
    refused <- expand z3 1 badSum expanded
    case refused of
        Left (NotDefinitional 2 _ (Just change)) -> do
            putStrLn $ "term: " <> show (changeTerm change)
            putStrLn $ "before: " <> show (changeBefore change)
            putStrLn $ "after: " <> show (changeAfter change)
            unless (changeTerm change == Node "add" [Node "one" [], Node "zero" []]) $ fail "wrong term"
            unless (changeBefore change == Just (changeTerm change)) $ fail "wrong meaning before"
            unless (changeAfter change == Just (Node "add" [Node "one" [], Node "one" []])) $ fail "wrong meaning after"
        _ -> fail "the bad extension was not refused as expected"
    unless (version expanded == 1) $ fail "the tower changed"

    putStrLn "step 4: the facts of the base stay"
    let facts = factsOf top
    forM_ (Map.toList facts) $ \(name, names) -> putStrLn $ show (D.productionNameText name) <> ": " <> show (map D.factNameText names)
    unless (Map.lookup "zero" facts == Just ["digit"]) $ fail "wrong facts of zero"
    unless (Map.lookup "add" facts == Just ["sum"]) $ fail "wrong facts of add"
    unless (Map.lookup "double" facts == Just []) $ fail "wrong facts of double"
    unless (L.exclusions top == L.exclusions base) $ fail "wrong exclusions"
    putStrLn $ "exclusions: " <> show (map L.exclusionNameText $ Map.keys $ L.exclusions top)
