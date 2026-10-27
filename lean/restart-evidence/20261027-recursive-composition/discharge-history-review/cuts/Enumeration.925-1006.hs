* @Right node@ is passed before expanding the node, so callers can drop a
  whole branch early when the node about to be expanded is already known to
  be uninteresting.
* @Left fragment@ is passed after expansion, together with the UVar it came
  from, so callers can reject the fragment or update their state before
  enumeration continues.

The threaded state parameter belongs entirely to the caller. Returning @True@
prunes the current nondeterministic branch; returning @False@ keeps it.

The 'ExpansionOrder' sees the same state and may steer which expandable UVar
goes next; 'noExpansionPreference' leaves that to the enumerator. An
unconstrained 'Mu' is never offered for expansion, so it is not expanded and
produces neither callback. Enumeration ends when no other UVar can be expanded.

Before the choice of an edge, the narrowing function can drop edges of the
node of the UVar. It sees the state and the UVar. A node without edges ends
the branch. The node expansion function expands the chosen node, for example
'enumerateNode'.

With a stop rule, enumeration also ends when the rule accepts every UVar that
is still to expand, the blocked ones included. The result is then the state at
that point. Without a stop rule, or at the end of the enumeration, the result
is 'Nothing'.
-}
enumerateUntil' ::
    forall symbol a.
    (Hashable symbol, Typeable symbol) =>
    Maybe (a -> UVar -> Bool) ->
    (a -> UVar -> Node symbol -> Node symbol) ->
    (Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)) ->
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    EnumerateM symbol (Maybe a)
enumerateUntil' stop narrow expandNode ost order oracle = case stop of
    Just rule -> do
        remaining <- gets _expandableUVars
        if not (IntSet.null remaining) && all (rule ost . intToUVar) (IntSet.toList remaining)
            then return (Just ost)
            else step
    Nothing -> step
  where
    step = do
        muv <- nextExpandableUVar (order ost)
        case muv of
            ExpansionStuck -> mzero
            ExpansionDone -> return Nothing
            ExpansionNext uv -> expandNext uv
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
                    _ -> expand n scs
