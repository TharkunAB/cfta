unconstrained recursive node is the base case of a recursion: expanding it
would unfold forever with nothing to stop it.
-}
expandable :: UVarValue symbol -> Bool
expandable (UVarUnenumerated (Just node) scs) = not (recursiveBoundary node && Sequence.null scs)
expandable _ = False
