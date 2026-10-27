    expandNext uv =
        let continue ost' = do
                tf <- enumerateOutUVarWith expandNode uv
                (should_prune, ost'') <- oracle ost' uv (Left tf)
                if should_prune
                    then mzero
                    else enumerateUntil' stop narrow expandNode ost'' order oracle
            expand n scs = do
                let narrowed = narrow ost uv n
                case narrowed of
                    EmptyNode -> mzero
                    _
                        | nodeIdentity narrowed == nodeIdentity n -> pure ()
                        | otherwise -> do
                            uv' <- getUVarRepresentative uv
                            setUVarValue uv' (UVarUnenumerated (Just narrowed) scs)
                (should_prune, ost') <- oracle ost uv (Right narrowed)
                if should_prune then mzero else continue ost'
         in do
