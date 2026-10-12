{-# LANGUAGE OverloadedStrings #-}

import Control.Monad (unless)
import qualified Data.CFTA.Formula as F
import qualified Data.CFTA.Gen.Refinement as G
import Data.CFTA.Index (everyRank)
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true, (.==))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

-- | Nested scopes that distinguish sparse and complete actual names.
guard :: Guard
guard =
    Substitute [Substitution (path [2]) (path [0])]
        $ Substitute [Substitution (path [0]) (path [3]), Substitution (path [1]) (path [4])]
        $ Satisfies (path [5]) (F.Atom F.Eq (F.Var "x") (F.Lit 0))

-- | One unconstrained nullary generator.
leaf :: Symbol -> G.LTAGen Int
leaf label = G.leaf (0 :: Int) label (const true)

-- | Both occurrences have the same complete subtree and refinement.
actual :: G.LTAGen Int
actual = G.refinedNode "a" (.== 0) noConstraint $ leaf "z"

-- | The complete witness rejects the only source candidate.
generator :: G.LTAGen (Int, Int, Int, Int, Int, Int)
generator =
    G.refinedNode "root" (const true) guard $
        (,,,,,) <$> actual <*> actual <*> leaf "b" <*> leaf "x" <*> leaf "y" <*> leaf "target"

-- | Compare complete witness checking with the compiler ambiguity gate.
main :: IO ()
main = withZ3 [] $ \solver -> do
    expected <- G.validOutcomes solver generator
    built <- G.compileWith solver generator
    print expected
    print (built >>= G.cardinality)
    print (built >>= \g -> G.cardinality g >>= traverse (G.unrank g) . everyRank)
    unless (expected == Right [] && (built >>= G.cardinality) == Left G.SolverUnknown) $
        fail "The compiler trusted an ambiguous sparse substitution."
