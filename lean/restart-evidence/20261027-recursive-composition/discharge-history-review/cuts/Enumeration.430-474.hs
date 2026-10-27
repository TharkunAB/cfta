{- | Replace the value of a UVar.

Unlike 'getUVarValue', this writes the UVar itself, not its representative.
'assimilateUvarVal' needs this to eliminate a UVar that was a representative
before a union.
-}
setUVarValue :: UVar -> UVarValue symbol -> EnumerateM symbol ()
setUVarValue uv val = do
    old <- gets (\s -> _uvarValues s IntMap.! uvarToInt uv)
    writeUVarValue (suspended val) (suspended old) uv val
  where
    suspended (UVarUnenumerated _ scs) = scs
    suspended _ = Sequence.Empty

{- | 'setUVarValue' with the suspended constraints that the slot gains and
loses, for a caller that knows them: the constraints that stay in the slot
change no count.
-}
writeUVarValue ::
    Seq SuspendedConstraint -> Seq SuspendedConstraint -> UVar -> UVarValue symbol -> EnumerateM symbol ()
writeUVarValue gained lost uv val =
    modify' $ \s ->
        s
            { _uvarValues = IntMap.insert idx val (_uvarValues s)
            , _expandableUVars =
                if expandable val
                    then IntSet.insert idx (_expandableUVars s)
                    else IntSet.delete idx (_expandableUVars s)
            , _waitingUVars = count (_uvarRepresentative s) 1 gained (count (_uvarRepresentative s) (-1) lost (_waitingUVars s))
            }
  where
    idx = uvarToInt uv
    count uf change scs waiting =
        Foldable.foldl' (\m sc -> IntMap.alter (add change) (uvarToInt (UnionFind.root (scGetUVar sc) uf)) m) waiting scs
    add change old = case maybe change (+ change) old of
        0 -> Nothing
        new -> Just new

{- | Whether a slot holds a node that enumeration can expand. An
unconstrained recursive node is the base case of a recursion: expanding it
would unfold forever with nothing to stop it.
-}
expandable :: UVarValue symbol -> Bool
expandable (UVarUnenumerated (Just node) scs) = not (recursiveBoundary node && Sequence.null scs)
expandable _ = False
