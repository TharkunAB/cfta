{-# LANGUAGE OverloadedStrings #-}

-- | Check the retained language and distribution repairs.
module Main (main) where

import Data.CFTA.Constraint (semanticConstraint)
import Data.CFTA.Formula (Sort (IntSort))
import qualified Data.CFTA.Gen.Refinement as G
import Data.CFTA.Ranked.Internal.Decoder (Plan (..), SizeClass (..))
import qualified Data.CFTA.Ranked.Internal.Size as Size
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (false, true, variable, (.>=))
import Data.CFTA.Refinement.Guard (argument, requires)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

-- | A tautological observation must preserve the bounded pair distribution.
atomicPair :: Entailment -> IO ()
atomicPair solver = do
    let atom = G.atomic $ G.frequency [(9, G.leaf (0 :: Int) "a" (const true)), (1, G.leaf 1 "b" (const true))]
        right = G.leaf (7 :: Int) "c" (const true)
        pair guard = G.refinedNode "pair" (const true) guard ((,) <$> atom <*> right)
        original = pair noConstraint
    putStrLn "Atomic pair: expected weights 9/10 and 1/10 before and after observation"
    putStrLn "Original PMF, bounded PMF, sizes"
    print $ G.pmf original
    print $ G.pmf $ G.upToSize 3 original
    print [G.sizeOfRank original rank | rank <- [0, 1]]
    observed <- G.compileWith solver $ pair $ requires (argument 0) (const true)
    putStrLn "Observed PMF, bounded PMF, sizes"
    print $ observed >>= G.pmf
    print $ observed >>= G.pmf . G.upToSize 3
    print $ fmap (\g -> [G.sizeOfRank g rank | rank <- [0, 1]]) observed
    case observed of
        Right compiled
            | G.pmf compiled == G.pmf original
            , G.pmf (G.upToSize 3 compiled) == G.pmf (G.upToSize 3 original)
            , [G.sizeOfRank compiled rank | rank <- [0, 1]] == [Just 3, Just 3] ->
                putStrLn "Atomic pair repair: PASS"
        _ -> fail "Observing the atomic pair changed its probability or size"

-- | Print the concrete accepted language through depth four.
printLanguage :: Entailment -> String -> Automaton -> IO ()
printLanguage solver label automaton = do
    putStrLn label
    result <- fmap (map eraseRefinements) <$> denotationAtMost solver 4 automaton
    print result
    case result of
        Right (_ : _) -> pure ()
        _ -> error "A root representative was lost."

-- | Removing the root's only accepted alternative must not empty its language.
rootRemoval :: Entailment -> IO ()
rootRemoval solver = do
    let leaf symbol = Node [Transition symbol true [] noConstraint]
        app symbol = Node [Transition "app" true [leaf symbol] noConstraint]
        accepted = Node [Transition "a" (variable "v" .>= 0) [] noConstraint]
        originalLeaf = Transition "b" true [] noConstraint
        falseRoot = semanticConstraint $ Satisfies (path []) false
        unresolvedFalse =
            semanticConstraint $
                Substitute
                    [ Substitution (path [1]) (path [3])
                    , Substitution (path [2]) (path [4])
                    ]
                    (Satisfies (path []) false)
        simple = Node [originalLeaf, Transition "f" true [accepted] falseRoot]
        compound = Node [originalLeaf, Transition "f" true [accepted, app "u", app "v", leaf "x", leaf "y"] unresolvedFalse]
        subtype = refinementSubtypingOn solver $ \edge ->
            if transitionSymbol edge `elem` ["a", "b"] then Just () else Nothing
        inspect label grammar = do
            putStrLn label
            printLanguage solver "Original" grammar
            inferred <- similarity subtype grammar
            case either (Left . show) Right inferred >>= either (Left . show) Right . minimize grammar of
                Left err -> putStrLn err
                Right minimized -> printLanguage solver "After minimize" minimized
            pruned <- prune solver grammar
            case pruned of
                Left err -> print err
                Right automaton -> do
                    putStrLn $ "Prune kept original: " <> show (automaton == grammar)
                    printLanguage solver "After prune" automaton
            reduced <- reduce solver subtype grammar
            case reduced of
                Left err -> print err
                Right minimized -> printLanguage solver "After reduce" minimized
    inspect "Root deletion: simple rejecting alternative" simple
    inspect "Root deletion: pruning retains an unresolved rejecting alternative" compound

-- | Check the internal product's positive-size assumption.
zeroProduct :: IO ()
zeroProduct = do
    let zeroFunction :: Size.SizeIndex (Int -> Int)
        zeroFunction = Size.sizeIndex $ PlanSized [SizeClass 0 1 (const id) (const id)]
        zeroValue :: Size.SizeIndex Int
        zeroValue = Size.sizeIndex $ PlanSized [SizeClass 0 1 (const 42) (const 42)]
        zeroZero = Size.productIndex zeroFunction zeroValue
        zeroOne = Size.productIndex zeroFunction $ Size.sizeIndex $ PlanSelect 1 (const 42)
        oneZero = Size.productIndex (Size.sizeIndex $ PlanSelect 1 (const id)) zeroValue
        token = Size.Occurrence 19
        productProbe = Size.productIndex zeroFunction $ Size.probeIndexWithMinimum token $ Size.MinimumSize 1
    putStrLn "Internal zero-size products: each lookup should count one member"
    print (Size.sizeClassCounts zeroZero, Size.countAtSize zeroZero 0)
    print (Size.sizeClassCounts zeroOne, Size.countAtSize zeroOne 1)
    print (Size.sizeClassCounts oneZero, Size.countAtSize oneZero 1)
    putStrLn "A zero-size sibling does not guard recursion: expected (True, True)"
    print (Size.isUnguarded token productProbe, Size.usesOccurrence token productProbe)

-- | Run the public regressions and the separate exposed-internal invariant check.
main :: IO ()
main = do
    withZ3 declarations $ \solver -> do
        atomicPair solver
        rootRemoval solver
    zeroProduct
  where
    declarations = [(name, IntSort) | name <- ["app", "x", "y", "v"]]
