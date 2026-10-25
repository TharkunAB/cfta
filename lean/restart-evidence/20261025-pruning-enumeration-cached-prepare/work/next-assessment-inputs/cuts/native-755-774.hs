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
