# Additive native callback evaluation caveat

Recorded 2026-10-24T04:51:35.931362+02:00. The frozen bridge plan remains unchanged (SHA4b55c8e8d57c65f5f16bc90701efd8f98e997063aeee90c0938626c00e1584ee). This note refines its later typedTypes heap-threading proposal. It does not change a current theorem or report a Haskell defect.

Pruning.hs124 uses `or <$> mapM (\h -> maybe False (emptyAt typing' h) <$> getUnexpandedNode (intToUVar h)) ...`. The native EnumerateM Functor/Pure/Monad definitions in Enumeration.hs328–351 pass result values without a bang or an explicit evaluation of each Boolean. The monadic getUnexpandedNode actions sequence their representative-compression state effects in ascending open-hole order. The final pure `or` can demand only a prefix of the resulting Boolean thunks. An earlier true flag need not force later pure emptyAt calls or their process-global interning work.

An explicit constructor-heap model must preserve that distinction. First collect the actual ordered optional-node observations while retaining the complete enumeration compression frame. Then evaluate the needed emptyAt predicates from left to right, stopping at the first true flag and carrying only the constructor heaps from the demanded calls. It must not stop the earlier monadic observation traversal at that true flag. It must not infer that all later native constructor calls occurred merely because all UVar reads occurred.

This concerns the interpretation of the pure source calls through explicit heap effects. Boolean agreement by itself does not establish exact allocation history. Invalid-slot/error forcing and whole native lazy error-stream correspondence remain separate; this note does not assert eager evaluation of every returned node projection. The current four-declaration encodeNode/lookupNode proposal is unaffected.

Source identities at this cut:

- `specftacular/src/Specftacular/Pruning.hs`: 16989 bytes, SHA-256 `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61`; cuts 113–141.

- `cfta/src/Data/CFTA/Enumeration.hs`: 71269 bytes, SHA-256 `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`; cuts 328–351,416–432,1412–1417.
