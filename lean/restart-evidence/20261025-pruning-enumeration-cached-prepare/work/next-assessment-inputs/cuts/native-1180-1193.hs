termsPruneUntil ::
    forall symbol a.
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Node symbol -> Node symbol) ->
    (a -> UVar -> Bool) ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    Node symbol ->
    [Term (PartialSymbol symbol)]
termsPruneUntil ost order narrow stop oracle n =
    map fst $ flip allBranches (initEnumerationState (canonicalEdgesOf Nothing n) n) $ do
        _ <- enumerateUntil' (Just stop) narrow enumerateShallowHere ost order oracle
        rootTermFrag >>= expandPartialTermFrag
