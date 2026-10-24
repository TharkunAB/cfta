# Next typing callback boundary

The typing callback must preserve the Mu-only exemptions in narrow and emptyAt.
The partial renderer uses recursiveBoundary, which also includes InternedUnion.
Do not replace the Mu-only test with that broader predicate.
This is a source-model obligation, not a newly found Haskell defect.

Source cuts and hashes:

specftacular/src/Specftacular/Pruning.hs:127-140
5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61
    narrow (_, types, _, typing) uv n = case n of
        Mu _ -> n
        _
            | uvarToInt uv `IntSet.member` types -> n
            | otherwise -> narrowAt n (holeKey typing (uvarToInt uv))
    emptyAt typing h n = case n of
        Mu _ -> False
        _ -> null (nodeEdges (narrowAt n (holeKey typing h)))
    -- One table for each call.
    narrowAt = memo2 (\n k -> Node [e | e <- nodeEdges n, keeps k e])
    keeps k e = case (edgeSymbol e, edgeChildren e) of
        ("app", [annotation, _, _, _]) -> admits k annotation
        ("filter", [annotation, _]) -> admits k annotation
        (symbol, [annotation]) -> admits k annotation && fits k symbol

280e52b5fd8ead27a6f44cabc489fdaa8aefe37b0e9f5520550f22cac3eea345

cfta/src/Data/CFTA/Interned/Type.hs:604-611
f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77
    ordinary (InternedNode node) = Just $ internedNodeEdges node
    ordinary _ = Nothing

-- | A node where finite diagnostic enumeration can stop before unfolding recursion.
recursiveBoundary :: Node symbol -> Bool
recursiveBoundary (InternedMu _) = True
recursiveBoundary (InternedUnion _) = True
recursiveBoundary _ = False

7011fbce7b56dd2ce297ddf8370ebacd4fef1b177d885a49f87b339c7856a1d2

cfta/src/Data/CFTA/Enumeration.hs:1038-1048
949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07
expandPartialTermFrag :: TermFragment symbol -> EnumerateM symbol (Term (PartialSymbol symbol))
expandPartialTermFrag (TermFragmentNode symbol children) =
    Term.traverseNode expandPartialTermFrag (ConcreteSymbol symbol) children
expandPartialTermFrag (TermFragmentUVar uv) = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandPartialTermFrag fragment
        UVarUnenumerated (Just node) Sequence.Empty | recursiveBoundary node -> return $ Term.Node TruncatedRecursion []
        _ -> return $ Term.Node (UVarHole uv) []

-- | Expand a complete term fragment into a concrete term, with the symbol that stands for truncated recursion.

08b0af7e19e5984b0f98748e6ad6146756c582ecb39ff6b6994867a1e5da8728
