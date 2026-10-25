inheritAncestry :: Int -> EnumerateM symbol ()
inheritAncestry idx = do
    current <- gets _expansionAncestry
    unless (HashSet.null current) $
        modify' $
            \s -> s{_recursionAncestry = IntMap.insertWith HashSet.union idx current (_recursionAncestry s)}
