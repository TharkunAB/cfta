{- | Build an edge with transition constraints.

The edge is empty when no term can meet its constraints: when 'contradictory'
says so, when its path equalities are contradictory, or when a path equality
names a child that the edge does not have (see 'fitsArity'). Enumeration and
'Data.CFTA.Equality.accepts' rely on this: they read the equality classes of an
edge without checking them.
-}
{-# INLINEABLE mkEdge #-}
mkEdge ::
    (Hashable symbol, Typeable symbol) =>
    symbol -> [Node symbol] -> Constraint -> Edge symbol
mkEdge s ns ecs
    | contradictory ecs || not (fitsArity (Arity (length ns)) (equalities ecs)) = emptyEdge s
    | otherwise = internEdge $ UninternedEdge s ns ecs
