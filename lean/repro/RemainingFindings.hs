{-# LANGUAGE OverloadedStrings #-}

-- | Reproduce the remaining findings after the three initial repairs.
module Main (main) where

import Data.CFTA.Constraint (semanticConstraint)
import Data.CFTA.Formula (Sort (IntSort))
import qualified Data.CFTA.Gen.Refinement as G
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (false, true, variable, (.>=))
import Data.CFTA.Refinement.Guard (argument, requires)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

-- | Print the concrete language through depth four.
printLanguage :: Entailment -> String -> Automaton -> IO ()
printLanguage solver label automaton = do
    putStrLn label
    print . fmap (map eraseRefinements) =<< denotationAtMost solver 4 automaton

-- | Compare two component transitions that have the same result type.
sameResultType :: Entailment -> Subtyping
sameResultType solver = refinementSubtypingOn solver $ \edge ->
    if transitionSymbol edge `elem` ["a", "b"] then Just () else Nothing

-- | Print direct minimization without an implicit pruning precondition.
printMinimized :: Entailment -> Automaton -> IO ()
printMinimized solver grammar = do
    inferred <- similarity (sameResultType solver) grammar
    case either (Left . show) Right inferred >>= either (Left . show) Right . minimize grammar of
        Left err -> putStrLn err
        Right minimized -> printLanguage solver "After minimize" minimized

-- | Print the language after pruning and minimization.
printReduced :: Entailment -> Automaton -> IO ()
printReduced solver grammar = do
    reduced <- reduce solver (sameResultType solver) grammar
    case reduced of
        Left err -> print err
        Right minimized -> printLanguage solver "After reduce" minimized

-- | Check non-atomic source sizes and representatives with rejected guards.
main :: IO ()
main = withZ3 declarations $ \solver -> do
    let original = G.oneof [G.leaf (0 :: Int) "a" (const true), G.node "wrap" $ G.leaf 1 "b" (const true)]
        built = G.ungroup $ G.keyed () original
        outer guard = G.refinedNode "outer" (const true) guard built
    putStrLn "Non-atomic built source: an observation must preserve these sizes and masses"
    print [G.sizeOfRank (outer noConstraint) rank | rank <- [0, 1]]
    compiled <- G.compileWith solver $ outer (requires (argument 0) (const true))
    print $ fmap (\g -> [G.sizeOfRank g rank | rank <- [0, 1]]) compiled
    print $ G.pmf $ G.upToSize 2 $ outer noConstraint
    print $ compiled >>= G.pmf . G.upToSize 2
    print $ fmap (\g -> map (G.smallerMembers g) [0, 1]) compiled

    let nested = G.node "pair" $ (,) <$> G.atomic original <*> G.leaf (7 :: Int) "c" (const true)
        nestedBuilt = G.ungroup $ G.keyed () nested
        nestedOuter guard = G.refinedNode "outer" (const true) guard nestedBuilt
    putStrLn "A non-atomic product with an atomic child must retain both equal-size members"
    print [G.sizeOfRank (nestedOuter noConstraint) rank | rank <- [0, 1]]
    nestedCompiled <- G.compileWith solver $ nestedOuter (requires (argument 0) (const true))
    print $ fmap (\g -> [G.sizeOfRank g rank | rank <- [0, 1]]) nestedCompiled
    print $ G.pmf $ G.upToSize 4 $ nestedOuter noConstraint
    print $ nestedCompiled >>= G.pmf . G.upToSize 4

    let leaf symbol = Node [Transition symbol true [] noConstraint]
        pairWith accepted rejected =
            Node
                [ Transition "f" true [rejected] noConstraint
                , Transition "f" true [accepted] noConstraint
                ]
        stronger = variable "v" .>= 0
        rejectedLeaf = Node [Transition "a" stronger [] $ semanticConstraint $ Satisfies (path []) false]
        direct = pairWith (leaf "b") rejectedLeaf
    putStrLn "A structurally productive representative whose own guard rejects it"
    printLanguage solver "Original" direct
    printMinimized solver direct
    printReduced solver direct

    let compound symbol = Node [Transition "app" true [leaf symbol] noConstraint]
        unresolvedFalse =
            semanticConstraint $
                Substitute
                    [ Substitution (path [0]) (path [2])
                    , Substitution (path [1]) (path [3])
                    ]
                    (Satisfies (path []) false)
        rejectedCompound =
            Node
                [Transition "a" stronger [compound "u", compound "v", leaf "x", leaf "y"] unresolvedFalse]
        retained = pairWith (leaf "b") rejectedCompound
    putStrLn "Pruning retains an unresolved guard on the rejected representative"
    printLanguage solver "Original" retained
    pruned <- prune solver retained
    case pruned of
        Left err -> print err
        Right automaton -> do
            putStrLn $ "Prune kept original: " <> show (automaton == retained)
            printLanguage solver "After prune" automaton
    printReduced solver retained
  where
    declarations = [(name, IntSort) | name <- ["app", "x", "y", "v"]]
