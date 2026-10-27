prepareShallowChild ::
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
prepareShallowChild scs n@(Node _)
    | not (any (isTerminalPathTrie . scGetPathTrie) scs) = do
        uv <- addUVarValue (Just n)
        setUVarValue uv (UVarUnenumerated (Just n) scs)
        pure (TermFragmentUVar uv)
prepareShallowChild scs n = enumerateNode scs n
