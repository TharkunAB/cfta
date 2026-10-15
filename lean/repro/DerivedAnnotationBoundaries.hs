{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Exception (SomeException, displayException, try)
import GHC.Generics (Generic)

import Data.CFTA.Gen.Refinement.Derive
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Index (Cardinality (..))
import qualified Data.CFTA.Refinement.Expression as Expr
import Data.CFTA.Refinement.Symbolic (Symbolic (..), true, (.&&))

-- | Keep one member after either annotation, so both cardinalities are finite.
data Choice = Probe | Control
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | A strict field forces its generic placeholder before constructor discrimination.
data Strict = Strict !Integer
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

instance HasLTA Strict where
    invariant = Contracted strictCheck

-- | This pattern follows the documented constructor discrimination rule.
strictCheck :: (Symbolic e) => Strict -> [e] -> Truth e
strictCheck Strict{} [value] = 0 .<= value .&& value .<= 1
strictCheck _ _ = true

-- | Preserve the observed result or exception of one public source call.
report :: String -> IO () -> IO ()
report label action = do
    putStrLn label
    observed <- try @SomeException action
    case observed of
        Left err -> putStrLn $ "exception: " <> displayException err
        Right () -> pure ()

-- | Compile the same root predicate after two named-measure annotations.
namedCardinality :: Integer -> IO ()
namedCardinality integer = do
    let annotation = measureNamed "m" (fromInteger integer :: Expr.Expr)
        annotations = [("Probe", annotation), ("Control", measureNamed "m" (0 :: Expr.Expr))]
    case deriveLTAWith @Choice 0 mempty annotations of
        Left err -> print err
        Right generator -> do
            compiled <-
                LTAGen.compile $
                    generator `LTAGen.satisfying` \value -> Expr.uninterpreted "m" [value] Expr..== 0
            let found = LTAGen.cardinality compiled
                expected = Right $ Cardinality $ if integer == 0 then 2 else 1
            print found
            putStrLn $ "expected cardinality: " <> show (if integer == 0 then 2 :: Integer else 1)
            putStrLn $ "matches expectation: " <> show (found == expected)

-- | Reproduce annotation projection loss and strict placeholder evaluation.
main :: IO ()
main = do
    let zero = measureNamed "m" (0 :: Expr.Expr)
        one = measureNamed "m" (1 :: Expr.Expr)
    putStrLn $ "annotationFormulas equal: " <> show (annotationFormulas zero == annotationFormulas one)
    report "Probe has m=0; Control has m=0; retain m=0:" $ namedCardinality 0
    report "Probe has m=1; Control has m=0; retain m=0:" $ namedCardinality 1
    report "Strict placeholder; documented Strict{} pattern:" $
        case deriveLTA @Strict 0 (atom @Integer $ LTAGen.elements [0, 1]) of
            Left err -> print err
            Right generator -> do
                compiled <- LTAGen.compile generator
                print $ LTAGen.cardinality compiled
