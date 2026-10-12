import Control.Monad (forM_, unless)
import qualified Data.CFTA.Equality as Equality
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (everyRank)
import qualified Data.CFTA.Term as Term

-- | Check recursive choices and spines before and after a finite bound.
main :: IO ()
main = do
    let chain :: Gen.Gen String Int
        chain = Gen.recur $ \self -> Gen.oneof [pure 0, Gen.node "s" $ (+ 1) <$> self]
        spine :: Gen.Gen String Int
        spine = Gen.recur $ \self -> (+) <$> Gen.oneof [pure 0, self] <*> Gen.elements [1, 2]
        apply generator = Gen.node "outer" $ (+) <$> generator <*> Gen.elements [10]
        generators =
            [chain, spine]
                <> [ wrap generator
                   | generator <- [chain, spine]
                   , wrap <- [Gen.node "outer", apply, Gen.node "outer" . Gen.upToSize 3, apply . Gen.upToSize 3]
                   ]
        baseline = Gen.upToSize 3 chain
    unless
        ( Gen.pmf baseline == Right [(value, 1 / 4) | value <- [0 .. 3]]
            && traverse (fmap Gen.surface . Gen.termAt baseline) [0 .. 3]
                == Right (take 4 $ iterate (\children -> [Term.Node "s" children]) [])
        )
        $ fail "The recursive boundary changed the values, probabilities, or surface terms."
    forM_ generators check
    putStrLn "Recursive support, inspection, and inverse ranks agree for all 10 bounded variants."

-- | Check every bounded rank against its support, inspection, and inverse.
check :: Gen.Gen String Int -> IO ()
check generator = do
    let bounded = Gen.upToSize 4 generator
    total <- either (fail . show) pure $ Gen.cardinality bounded
    support <- either (fail . show) pure $ Gen.support bounded
    inspection <- either (fail . show) pure $ Gen.inspect bounded
    forM_ (everyRank total) $ \rank -> do
        term <- either (fail . show) pure $ Gen.termAt bounded rank
        ranks <- either (fail . show) pure $ Gen.ranksOf bounded term
        let inspected = fmap (\symbol -> Gen.InspectionSymbol symbol Nothing) term
        unless
            ( Equality.accepts support term
                && Equality.accepts (Gen.inspectionGraph inspection) inspected
                && rank `elem` ranks
            )
            $ fail
            $ "Recursive support or inverse rejects " <> show (rank, term)
