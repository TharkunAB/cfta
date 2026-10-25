expandable :: UVarValue symbol -> Bool
expandable (UVarUnenumerated (Just node) scs) = not (recursiveBoundary node && Sequence.null scs)
expandable _ = False

---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM symbol SuspendedConstraint
pecToSuspendedConstraint pec = do
    uv <- addUVarValue Nothing
    return $ SuspendedConstraint (getPathTrie pec) uv

