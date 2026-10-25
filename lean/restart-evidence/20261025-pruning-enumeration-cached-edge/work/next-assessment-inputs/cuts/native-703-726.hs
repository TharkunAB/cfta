canonicalEdgesOf weights root = edgesOf
  where
    byWeights = maybe id byWeight weights
    ordered = IntMap.map byWeights (canonicalOrder root)
    edgesOf n =
        let NodeId ident = nodeIdentity n
         in fromMaybe (byWeights (canonicalEdges n)) (IntMap.lookup ident ordered)

-- | Enumerate one node under the suspended constraints currently in scope.
enumerateNode ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
enumerateNode _ EmptyNode = mzero
enumerateNode scs n =
    let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
     in case hereConstraints of
            Sequence.Empty -> case n of
                Mu _ -> TermFragmentUVar <$> addUVarValue (Just n)
                InternedUnion _ -> TermFragmentUVar <$> addUVarValue (Just n)
                Node _ -> do
                    edgesOf <- gets _edgesOf
                    enumerateEdge scs =<< branches (edgesOf n)
                Rec recId ->
