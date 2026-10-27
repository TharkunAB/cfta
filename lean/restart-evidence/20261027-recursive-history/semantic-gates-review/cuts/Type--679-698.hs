
A 'Mu' whose variable does not occur in its body binds nothing, so the body is returned on its own. Intersection
already avoids introducing such nodes (see @maybeMu@); doing it here covers every recursive node, however it was
built. A 'Mu' whose body is its own variable accepts no term, so it is 'EmptyNode'. Its unfolding is the node itself,
so an operation that unfolds it would not stop.

Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
for performance considerations.
-}
{-# INLINEABLE createMu #-}
createMu ::
    (Typeable symbol) => (Node symbol -> Node symbol) -> Node symbol
createMu = dropRedundantMu . createMuDontCleanup
  where
    dropRedundantMu :: Node symbol -> Node symbol
    dropRedundantMu node@(InternedMu mu)
        | RecInt (internedMuId mu) `Set.notMember` freeVars (internedMuBody mu) = internedMuBody mu
        | Rec (RecInt identity) <- internedMuBody mu, identity == internedMuId mu = EmptyNode
        | otherwise = node
    dropRedundantMu node = node
