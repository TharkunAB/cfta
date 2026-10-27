-- | A node where finite diagnostic enumeration can stop before unfolding recursion.
recursiveBoundary :: Node symbol -> Bool
recursiveBoundary (InternedMu _) = True
recursiveBoundary (InternedUnion _) = True
recursiveBoundary _ = False
