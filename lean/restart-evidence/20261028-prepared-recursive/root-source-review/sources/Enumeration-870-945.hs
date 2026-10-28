                        _ -> intToUVar (IntSet.findMin candidates)

{- | Expand one selected slot into a fragment with the supplied node-expansion
function.

The pattern bind is deliberately failable: a failed match in 'EnumerateM'
ends the branch, so a UVar that is not an unexpanded node drops this branch
instead of raising. The branch is unreachable through @enumerateFully'@, which takes its
UVar from 'nextExpandableUVar' and so only offers expandable UVars.
-}
enumerateOutUVarWith ::
    (Hashable symbol, Typeable symbol) =>
    (Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)) ->
    UVar ->
    EnumerateM symbol (TermFragment symbol)
enumerateOutUVarWith expandNode uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv
        ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt uv') . _recursionAncestry
        modify' $ \s ->
            s
                { _expansionAncestry = if recursiveBoundary n then HashSet.insert (recursionKey n scs) ancestry else ancestry
                }

        t <- case n of
            Mu _ -> expandNode scs (unfoldOuterRec n)
            InternedUnion _ -> expandNode scs (Node $ nodeEdges n)
            _ -> expandNode scs n

        modify' $ \s -> s{_expansionAncestry = HashSet.empty}
        setUVarValue uv' (UVarEnumerated t)
        return t

-- | Expand the root UVar until it represents a complete term.
enumerateFully :: (Hashable symbol, Typeable symbol) => EnumerateM symbol ()
enumerateFully =
    enumerateFully' () noExpansionPreference (\state _ _ -> return (False, state))

{- | 'enumerateUntil'' without a stop rule and without narrowing: enumerate
until the root term is complete.
-}
enumerateFully' ::
    forall symbol a.
    (Hashable symbol, Typeable symbol) =>
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    EnumerateM symbol ()
enumerateFully' ost order oracle = void (enumerateUntil' Nothing (\_ _ n -> n) enumerateNode ost order oracle)

{- | Enumerate until the root term is complete, with optional oracle pruning.

The oracle is called twice around each UVar it expands:

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
