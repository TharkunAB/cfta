canonicalEdgesOf ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Maybe (Edge symbol -> Double) -> Node symbol -> Node symbol -> [Edge symbol]
canonicalEdgesOf weights root = edgesOf
  where
    byWeights = maybe id byWeight weights
    ordered = IntMap.map byWeights (canonicalOrder root)
    edgesOf n =
        let NodeId ident = nodeIdentity n
         in fromMaybe (byWeights (canonicalEdges n)) (IntMap.lookup ident ordered)
