module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.ExtensionSpec
import qualified Data.CFTA.Gen.Equality.DatatypeGenSpec
import qualified Data.CFTA.Gen.Equality.GenSpec
import qualified Data.CFTA.Gen.Equality.IFCExpressionGenSpec
import qualified Data.CFTA.Gen.Equality.RankDecodingSpec
import qualified Data.CFTA.Gen.Equality.RecursiveGenSpec
import qualified Data.CFTA.Gen.Equality.SimpleSpec
import qualified Data.CFTA.Gen.Equality.TypedExpressionGenSpec
import qualified Data.CFTA.Gen.ExpressionLanguageSpec
import qualified Data.CFTA.Gen.ReferenceSpec
import qualified Data.CFTA.Gen.Synthesis.StatesSpec
import qualified Data.CFTA.Gen.SynthesisSpec
import qualified Data.CFTA.Gen.TowerSpec
import qualified Data.CFTA.Gen.TypingSpec
import qualified Data.CFTA.GenSpec
import qualified Data.CFTA.GuidedSpec
import qualified Data.CFTA.InclusionSpec
import qualified Data.CFTA.Mask.TextSpec
import qualified Data.CFTA.Mask.VocabularySpec
import qualified Data.CFTA.MaskSpec
import qualified Data.CFTA.RankedSpec
import qualified Data.CFTA.Sized.Prefix.TrainSpec
import qualified Data.CFTA.Sized.PrefixGuardSpec
import qualified Data.CFTA.Sized.PrefixSpec
import qualified Data.CFTA.SizedSpec
import qualified Data.CFTA.TowerSpec
import qualified Data.CFTA.TraceSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.RankedSpec.spec
        Data.CFTA.GenSpec.spec
        Data.CFTA.GuidedSpec.spec
        Data.CFTA.MaskSpec.spec
        Data.CFTA.Mask.TextSpec.spec
        Data.CFTA.Mask.VocabularySpec.spec
        Data.CFTA.Gen.Equality.DatatypeGenSpec.spec
        Data.CFTA.Gen.Equality.GenSpec.spec
        Data.CFTA.Gen.Equality.IFCExpressionGenSpec.spec
        Data.CFTA.Gen.Equality.RankDecodingSpec.spec
        Data.CFTA.Gen.Equality.RecursiveGenSpec.spec
        Data.CFTA.Gen.Equality.SimpleSpec.spec
        Data.CFTA.Gen.Equality.TypedExpressionGenSpec.spec
        Data.CFTA.Gen.ExpressionLanguageSpec.spec
        Data.CFTA.Gen.ReferenceSpec.spec
        Data.CFTA.Gen.SynthesisSpec.spec
        Data.CFTA.Gen.Synthesis.StatesSpec.spec
        Data.CFTA.Gen.TowerSpec.spec
        Data.CFTA.Gen.TypingSpec.spec
        Data.CFTA.SizedSpec.spec
        Data.CFTA.Sized.PrefixSpec.spec
        Data.CFTA.Sized.Prefix.TrainSpec.spec
        Data.CFTA.Sized.PrefixGuardSpec.spec
        Data.CFTA.ExtensionSpec.spec
        Data.CFTA.TowerSpec.spec
        Data.CFTA.InclusionSpec.spec
        Data.CFTA.TraceSpec.spec
