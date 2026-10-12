import Control.Monad (forM_, unless)
import qualified Data.CFTA.Enumeration as Enumeration
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (everyRank)
import qualified Data.Set as Set

-- | Check grouped function spines, including correlated and nested alternatives.
main :: IO ()
main = do
    let retain = Gen.atKey () . Gen.groupOn (const ())
        source :: Gen.Gen String Int
        source = pure id <*> Gen.elements [0, 1]
        correlated =
            uncurry (+)
                <$> Gen.atKey
                    True
                    (Gen.groupOn (uncurry (==)) $ (,) <$> Gen.elements [0, 1] <*> Gen.elements [0, 1])
        sources =
            [ retain source
            , (+) <$> retain source <*> Gen.elements [10, 11]
            , retain $ (+) <$> retain source <*> Gen.elements [10, 11]
            , correlated
            , retain $ pure 0
            , retain $ Gen.elements [0, 1]
            , retain $ Gen.oneof [pure 0, source, Gen.leaf 2 "atom"]
            ]
    forM_ sources $ \functions -> do
        let generator = Gen.node "outer" $ (+) <$> functions <*> Gen.elements [100]
            marker = Gen.Label "unused-recursion-marker"
        total <- either (fail . show) pure $ Gen.cardinality generator
        selected <- either (fail . show) pure $ traverse (Gen.termAt generator) (everyRank total)
        support <- either (fail . show) pure $ Gen.support generator
        inspection <- either (fail . show) pure $ Gen.inspect generator
        let actual = Set.fromList $ Enumeration.termsWith marker support
            inspected =
                Set.fromList
                    $ map (fmap Gen.originalSymbol)
                    $ Enumeration.termsWith (Gen.InspectionSymbol marker Nothing) (Gen.inspectionGraph inspection)
            expected = Set.fromList selected
        unless (actual == expected && inspected == expected) $
            fail "Grouped function-spine support differs from the selected terms."
        forM_ (zip (everyRank total) selected) $ \(rank, term) -> do
            ranks <- either (fail . show) pure $ Gen.ranksOf generator term
            unless (rank `elem` ranks) $ fail "The grouped function-spine term lost its inverse rank."
    putStrLn "Support, inspection, and inverse ranks agree for all 7 grouped function-spine variants."
