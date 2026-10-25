instance MonadFail (EnumerateM symbol) where
    {-# INLINE fail #-}
    fail _ = empty

-- | Like @StateT@ from "Control.Monad.State.Strict", 'state' forces the pair that its function gives.
instance MonadState (EnumerationState symbol) (EnumerateM symbol) where
    {-# INLINE state #-}
    state f = EnumerateM $ \s success later -> case f s of (a, s') -> success a s' later

-- | One branch for each element, in order.
branches :: [a] -> EnumerateM symbol a
{-# INLINE branches #-}
branches xs = EnumerateM $ \s success later -> foldr (\x rest -> success x s rest) later xs

-- | The result and the final state of every branch, in order, lazily.
allBranches :: EnumerateM symbol a -> EnumerationState symbol -> [(a, EnumerationState symbol)]
