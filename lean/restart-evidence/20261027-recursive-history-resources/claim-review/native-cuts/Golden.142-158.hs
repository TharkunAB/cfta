
main :: IO ()
main = do
    accept <- (== Just "1") <$> lookupEnv "GOLDEN_ACCEPT"
    results <- mapM (check accept) cases
    unless (and results) exitFailure

{- | The laws of a signature with terms up to a size in the monomorphic
phase, as 'discoverMonomorphic', with or without the test of the types.
-}
monomorphic :: Bool -> Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> [Sig] -> IO [String]
monomorphic = withOrder (KnuthBendix mempty)

-- | 'monomorphic' with a term order.
withOrder :: TermOrder -> Bool -> Int -> (TypeSkeleton -> Maybe GeneratedInstance) -> [Sig] -> IO [String]
withOrder order checked size =
    experimentalPhases ((defaultOptions size 1){searchChecked = checked, searchTermOrder = order, searchDefinitions = True})
