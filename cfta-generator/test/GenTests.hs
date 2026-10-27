module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Edit.SetsSpec
import qualified Data.CFTA.Edit.TreesSpec
import qualified Data.CFTA.Edit.BetweenSpec
import qualified Data.CFTA.Edit.ConstrainedSpec
import qualified Data.CFTA.EditSpec
import qualified Data.CFTA.Gen.CompiledRankSpec
import qualified Data.CFTA.ExtensionSpec
import qualified Data.CFTA.Gen.Equality.DatatypeGenSpec
import qualified Data.CFTA.Gen.Equality.GenSpec
import qualified Data.CFTA.Gen.Equality.IFCExpressionGenSpec
import qualified Data.CFTA.Gen.Equality.RankDecodingSpec
import qualified Data.CFTA.Gen.Equality.RecursiveGenSpec
import qualified Data.CFTA.Gen.Equality.SimpleSpec
import qualified Data.CFTA.Gen.Equality.TypedExpressionGenSpec
import qualified Data.CFTA.Gen.InvertibleSpec
import qualified Data.CFTA.Gen.IndexedLeafSpec
import qualified Data.CFTA.Gen.ManySorted.RefinedSpec
import qualified Data.CFTA.Gen.ManySorted.ScopedSpec
import qualified Data.CFTA.Gen.ManySortedSpec
import qualified Data.CFTA.Gen.ReferenceSpec
import qualified Data.CFTA.Gen.Synthesis.StatesSpec
import qualified Data.CFTA.Gen.SynthesisSpec
import qualified Data.CFTA.Gen.TypingSpec
import qualified Data.CFTA.Gen.ValueSortsSpec
import qualified Data.CFTA.GenSpec
import qualified Data.CFTA.InclusionSpec
import qualified Data.CFTA.RankedSpec
import qualified Data.CFTA.Sized.PrefixGuardSpec
import qualified Data.CFTA.Sized.PrefixSpec
import qualified Data.CFTA.SizedSpec
import qualified Data.CFTA.Template.LearnSpec
import qualified Data.CFTA.Template.NamedSpec
import qualified Data.CFTA.TraceSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.RankedSpec.spec
        Data.CFTA.Gen.CompiledRankSpec.spec
        Data.CFTA.GenSpec.spec
        Data.CFTA.Gen.Equality.DatatypeGenSpec.spec
        Data.CFTA.Gen.Equality.GenSpec.spec
        Data.CFTA.Gen.Equality.IFCExpressionGenSpec.spec
        Data.CFTA.Gen.Equality.RankDecodingSpec.spec
        Data.CFTA.Gen.Equality.RecursiveGenSpec.spec
        Data.CFTA.Gen.Equality.SimpleSpec.spec
        Data.CFTA.Gen.Equality.TypedExpressionGenSpec.spec
        Data.CFTA.Gen.InvertibleSpec.spec
        Data.CFTA.Gen.IndexedLeafSpec.spec
        Data.CFTA.Gen.ManySorted.RefinedSpec.spec
        Data.CFTA.Gen.ManySorted.ScopedSpec.spec
        Data.CFTA.Gen.ManySortedSpec.spec
        Data.CFTA.Gen.ReferenceSpec.spec
        Data.CFTA.Gen.SynthesisSpec.spec
        Data.CFTA.Gen.Synthesis.StatesSpec.spec
        Data.CFTA.Gen.TypingSpec.spec
        Data.CFTA.Gen.ValueSortsSpec.spec
        Data.CFTA.SizedSpec.spec
        Data.CFTA.InclusionSpec.spec
        Data.CFTA.Template.LearnSpec.spec
        Data.CFTA.Template.NamedSpec.spec
        Data.CFTA.Edit.SetsSpec.spec
        Data.CFTA.Edit.TreesSpec.spec
        Data.CFTA.Edit.BetweenSpec.spec
        Data.CFTA.EditSpec.spec
        Data.CFTA.Edit.ConstrainedSpec.spec
        Data.CFTA.TraceSpec.spec
        Data.CFTA.Sized.PrefixSpec.spec
        Data.CFTA.Sized.PrefixGuardSpec.spec
        Data.CFTA.ExtensionSpec.spec
