import Control.Monad (unless)
import qualified Data.CFTA.Enumeration as Enumeration
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (everyRank)
import qualified Data.Set as Set

-- | Compare grouped support and inspection with every decoded member term.
main :: IO ()
main = do
    let source :: Gen.FTAGen String (Int, Int)
        source = (,) <$> Gen.elements [0, 1] <*> Gen.elements [0, 1]
        generator = Gen.ungroup $ Gen.node "group" $ Gen.groupOn (\(a, b) -> (a + b) `mod` 2) source
        marker = Gen.Label "unused-recursion-marker"
    total <- either (fail . show) pure $ Gen.cardinality generator
    terms <- either (fail . show) pure $ traverse (Gen.termAt generator) (everyRank total)
    support <- either (fail . show) pure $ Gen.support generator
    inspection <- either (fail . show) pure $ Gen.inspect generator
    let expected = Set.fromList terms
        actual = Set.fromList $ Enumeration.termsWith marker support
        inspected =
            Set.fromList
                $ map (fmap Gen.originalSymbol)
                $ Enumeration.termsWith (Gen.InspectionSymbol marker Nothing) (Gen.inspectionGraph inspection)
    unless (actual == expected && inspected == expected)
        $ fail
        $ "missing support terms: " <> show (expected Set.\\ actual) <> "; extra support terms: " <> show (actual Set.\\ expected)
    putStrLn $ "Support and inspection match all " <> show total <> " decoded terms."
