module Main (main) where

import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (hspec)

import qualified Data.CFTA.Gen.Refinement.BoundedGeneratorSpec
import qualified Data.CFTA.Gen.Refinement.CompileSpec
import qualified Data.CFTA.Gen.Refinement.DependentApplicationSpec
import qualified Data.CFTA.Gen.Refinement.DeriveSpec
import qualified Data.CFTA.Gen.Refinement.ListTheorySpec
import qualified Data.CFTA.Gen.Refinement.OracleSpec
import qualified Data.CFTA.Gen.Refinement.PreconditionTypedExpressionSpec
import qualified Data.CFTA.Gen.Refinement.QuickCheckSyntaxSpec
import qualified Data.CFTA.Gen.Refinement.RecursiveGeneratorSpec
import qualified Data.CFTA.Gen.Refinement.SafeBufferSpec
import qualified Data.CFTA.Gen.Refinement.SimilarityMinimizationSpec
import qualified Data.CFTA.Gen.Refinement.SizedVectorSpec
import qualified Data.CFTA.Gen.Refinement.StateMachineTraceSpec
import qualified Data.CFTA.Gen.Refinement.SubsumptionTypedExpressionSpec
import qualified Data.CFTA.Gen.Refinement.TraceSpec
import qualified Data.CFTA.Gen.Refinement.TypedLanguageSpec
import qualified Data.CFTA.Gen.Synthesis.HybridSpec
import qualified Data.CFTA.Gen.Synthesis.LiquidSpec

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec $ do
        Data.CFTA.Gen.Refinement.QuickCheckSyntaxSpec.spec
        Data.CFTA.Gen.Refinement.CompileSpec.spec
        Data.CFTA.Gen.Refinement.RecursiveGeneratorSpec.spec
        Data.CFTA.Gen.Refinement.BoundedGeneratorSpec.spec
        Data.CFTA.Gen.Refinement.SafeBufferSpec.spec
        Data.CFTA.Gen.Refinement.PreconditionTypedExpressionSpec.spec
        Data.CFTA.Gen.Refinement.SubsumptionTypedExpressionSpec.spec
        Data.CFTA.Gen.Refinement.TypedLanguageSpec.spec
        Data.CFTA.Gen.Refinement.SimilarityMinimizationSpec.spec
        Data.CFTA.Gen.Refinement.SizedVectorSpec.spec
        Data.CFTA.Gen.Refinement.StateMachineTraceSpec.spec
        Data.CFTA.Gen.Refinement.TraceSpec.spec
        Data.CFTA.Gen.Refinement.DependentApplicationSpec.spec
        Data.CFTA.Gen.Refinement.OracleSpec.spec
        Data.CFTA.Gen.Refinement.DeriveSpec.spec
        Data.CFTA.Gen.Refinement.ListTheorySpec.spec
        Data.CFTA.Gen.Synthesis.LiquidSpec.spec
        Data.CFTA.Gen.Synthesis.HybridSpec.spec
