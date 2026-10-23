module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Gen.Equality.DatatypeGenSpec
import qualified Data.CFTA.Gen.Equality.GenSpec
import qualified Data.CFTA.Gen.Equality.IFCExpressionGenSpec
import qualified Data.CFTA.Gen.Equality.RankDecodingSpec
import qualified Data.CFTA.Gen.Equality.RecursiveGenSpec
import qualified Data.CFTA.Gen.Equality.SimpleSpec
import qualified Data.CFTA.Gen.Equality.TypedExpressionGenSpec
import qualified Data.CFTA.Gen.IndexedLeafSpec
import qualified Data.CFTA.Gen.ManySortedSpec
import qualified Data.CFTA.Gen.ReferenceSpec
import qualified Data.CFTA.Gen.Synthesis.StatesSpec
import qualified Data.CFTA.Gen.SynthesisSpec
import qualified Data.CFTA.Gen.TypingSpec
import qualified Data.CFTA.Gen.ValueSortsSpec
import qualified Data.CFTA.GenSpec
import qualified Data.CFTA.RankedSpec
import qualified Data.CFTA.SizedSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.RankedSpec.spec
        Data.CFTA.GenSpec.spec
        Data.CFTA.Gen.Equality.DatatypeGenSpec.spec
        Data.CFTA.Gen.Equality.GenSpec.spec
        Data.CFTA.Gen.Equality.IFCExpressionGenSpec.spec
        Data.CFTA.Gen.Equality.RankDecodingSpec.spec
        Data.CFTA.Gen.Equality.RecursiveGenSpec.spec
        Data.CFTA.Gen.Equality.SimpleSpec.spec
        Data.CFTA.Gen.Equality.TypedExpressionGenSpec.spec
        Data.CFTA.Gen.IndexedLeafSpec.spec
        Data.CFTA.Gen.ManySortedSpec.spec
        Data.CFTA.Gen.ReferenceSpec.spec
        Data.CFTA.Gen.SynthesisSpec.spec
        Data.CFTA.Gen.Synthesis.StatesSpec.spec
        Data.CFTA.Gen.TypingSpec.spec
        Data.CFTA.Gen.ValueSortsSpec.spec
        Data.CFTA.SizedSpec.spec
