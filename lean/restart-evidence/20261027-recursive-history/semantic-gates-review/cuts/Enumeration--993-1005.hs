                UVarUnenumerated (Just n) scs <- getUVarValue uv
                case n of
                    _ | recursiveBoundary n -> do
                        uv' <- getUVarRepresentative uv
                        ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt uv') . _recursionAncestry
                        if HashSet.member (recursionKey n scs) ancestry
                            then do
                                -- The expansion of this node with these paths led to it
                                -- again, so each further expansion repeats the last one.
                                -- Enumeration stops here, as at an unconstrained 'Mu'.
                                setUVarValue uv' (UVarUnenumerated (Just n) Sequence.Empty)
                                enumerateUntil' stop narrow expandNode ost order oracle
                            else expand n scs
