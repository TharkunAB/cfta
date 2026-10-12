{-# LANGUAGE OverloadedStrings #-}

-- | Reject a self-dependent measure before a parent can lose accepted points.
module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.CFTA.Formula as Formula
import qualified Data.CFTA.Gen.Refinement.QuickCheck as Gen
import Data.CFTA.Refinement (Guard (Holds, Satisfies), contractTermName, noConstraint, path)
import Data.CFTA.Refinement.Expression
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Symbol (valueName)
import Data.String (fromString)

-- | Two finite integer points leave their symbolic measure open.
digits :: Gen.LTAGen Integer
digits = Gen.every `Gen.satisfying` (\v -> 0 .<= v .&& v .<= 1)

main :: IO ()
main = withZ3 [(fromString valueName, Formula.IntSort)] $ \solver -> do
    let measured left right = Gen.measuredNode "m" noConstraint (+) $ (,) <$> left <*> right
        self = Gen.leaf (0 :: Integer) "self" (\v -> v .== v)
        rejecting = [Satisfies (path [0]) Formula.Bottom, Holds [path [0]] Formula.Bottom]
    forM_ [digits, Gen.elements [0, 1]] $ \right ->
        forM_ rejecting $ \guard -> do
            let generator = Gen.refinedNode "p" (const true) guard $ measured self right
            compiled <- Gen.compileWith solver generator
            oracle <- Gen.validOutcomes solver generator
            unless (fmap Gen.cardinality compiled == Left (Gen.InexactMeasure "m") && oracle == Left (Gen.InexactMeasure "m")) $
                fail "A self-dependent child did not report InexactMeasure."
    let accepted value =
            [ Satisfies (path [0]) $ refinementFormula (.== literal value)
            , Holds [path [0]] $ variable (contractTermName 0) .== literal value
            ]
        controls =
            [ (Gen.leaf (0 :: Integer) "zero" (.== 0), 1, [(0, 1)])
            , (Gen.leaf 7 "singleton" (\v -> v .== v * 0 + 3), 3, [(7, 0)])
            ]
    forM_ controls $ \(left, measure, expected) ->
        forM_ (accepted (measure :: Integer)) $ \guard -> do
            let generator = Gen.refinedNode "p" (const true) guard $ measured left digits
            compiled <- Gen.compileWith solver generator
            oracle <- Gen.validOutcomes solver generator
            unless (fmap Gen.values compiled == Right (Right expected) && oracle == Right expected) $
                fail "An independent or singleton measure changed."
    putStrLn "Self-dependent measures reject; independent and singleton measures retain both parent guard forms."
