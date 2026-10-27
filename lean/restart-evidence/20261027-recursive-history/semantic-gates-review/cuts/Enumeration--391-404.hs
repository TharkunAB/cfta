addUVarValue :: Maybe (Node symbol) -> EnumerateM symbol UVar
addUVarValue x = do
    uv <- nextUVar
    let value = UVarUnenumerated x Sequence.Empty
    modify' $ \s ->
        s
            { _uvarValues = IntMap.insert (uvarToInt uv) value (_uvarValues s)
            , _expandableUVars =
                if expandable value
                    then IntSet.insert (uvarToInt uv) (_expandableUVars s)
                    else _expandableUVars s
            }
    inheritAncestry (uvarToInt uv)
    return uv
