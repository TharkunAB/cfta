-- | Prepare the children of one selected edge with the supplied function.
enumerateEdgeWith ::
    (Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)) ->
    Seq SuspendedConstraint ->
    Edge symbol ->
    EnumerateM symbol (TermFragment symbol)
enumerateEdgeWith prepareChild scs e = do
    let inherited = descendScs IntMap.empty scs
    -- The inherited obligations must fit the edge. Its own classes fit it.
    guard $ maybe True (\(highest, _) -> compareLength (edgeChildren e) highest == GT) (IntMap.lookupMax inherited)

    newScs <- mapM pecToSuspendedConstraint (unsafeGetEclasses $ equalities $ edgeConstraint e)
    let children = descendScs inherited newScs
    fragment <-
        TermFragmentNode (edgeSymbol e)
            <$> zipWithM (\i n -> prepareChild (IntMap.findWithDefault Sequence.Empty i children) n) [0 ..] (edgeChildren e)
    when (residual (edgeConstraint e)) $
        modify' $
            \s -> s{_obligations = (edgeConstraint e, fragment) : _obligations s}
    return fragment

{- | Expand one ordinary node and defer its eligible children.
Keep the existing preparation of terminal equality endpoints and recursive
boundaries. A selected root must not defer itself into another fresh slot.
-}
enumerateShallowHere ::
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
enumerateShallowHere scs n@(Node _)
    | not (any (isTerminalPathTrie . scGetPathTrie) scs) = do
        edgesOf <- gets _edgesOf
        enumerateEdgeWith prepareShallowChild scs =<< branches (edgesOf n)
enumerateShallowHere scs n = enumerateNode scs n

{- | Keep an ordinary child in a slot until the ready-hole loop selects it.
Install its full suspended constraints through the existing waiting counter.
Terminal endpoints still merge through the existing node-preparation path.
-}
prepareShallowChild ::
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
prepareShallowChild scs n@(Node _)
    | not (any (isTerminalPathTrie . scGetPathTrie) scs) = do
        uv <- addUVarValue (Just n)
        setUVarValue uv (UVarUnenumerated (Just n) scs)
        pure (TermFragmentUVar uv)
prepareShallowChild scs n = enumerateNode scs n
