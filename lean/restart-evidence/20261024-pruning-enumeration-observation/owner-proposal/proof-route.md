# Proposed observation proof route

1. PendingRealized is the literal indexed-slot predicate in definition-contract.json. It uses the actual computed cache lookup. It never receives a decoder, replacement graph, desired returned Value or final-state oracle.
2. initial_realized calls available_readback to derive the handle. Cases on the actual initial list index establish the predicate for its single pending slot. No input encode/lookup success is assumed.
3. realized_preserved rewrites a stored after-slot with Frame.values, obtains its actual old complete Value, then uses lookupNode_keeps and Available.grows with exactly kept.growth and kept.history. Closedness concerns that unchanged Value.
4. observed_realized inverts the actual getUnexpandedNode and getValue successes. Their stored representative slot determines the pending handle. The pending-slot predicate derives the full native Value and its availability/closedness. getValue_frame supplies the complete final core Frame under Total.
5. observation_complete obtains a real root path from storage.total and a finite findRoot execution from findRoot_terminates. findRoot_bounded and storage.aligned place the returned root inside the actual values list. The active Lean4.34.1 List.getElem?_eq_getElem lemma supplies the exact stored element. Construct the actual getValue and getUnexpandedNode successes with the existing inversion/construction iff lemmas. Use observed_realized for each some outcome.

Total alone cannot supply a stored value-table element. The finite producer requires StorageValid and uv<before.counter. It does not require an assumed successful observer, Safe, Ready-to-expand, Finished, a root premise or a native Ready heap. The existence theorem retains the actual full final compression state; it does not identify fuels across different forests.

The scoped types list every proposed obtain, let, have, intro and constructor/Option specialization. No helper, new type, instance, induction or IH is planned. The observation_complete call to the earlier public observed_realized theorem is an acyclic dependency.

Target120–165 ordinary lines; hard180. The38 context/header lines plus roughly65–95 proof/definition lines and short comments fit this range. A smaller source is permitted without padding. Root must approve the exact declaration package and separately authorize a complete body before compiler work.

The module establishes initial realization and observation/cache-growth preservation. Actual slot writes, intersection/assimilation, the driver's narrowed-node write, and open-hole metadata bounds remain later producer obligations. Source NodeId extraction and full graph realization are not claimed.

Later typedTypes composition must sequence all ordered UF observation actions before the pure or result. Its pure emptyAt calls may be demanded only for a prefix. Preserve the native heap effects of that prefix and keep all earlier UF compression effects. The separate frozen laziness caveat remains applicable. No full lazy error-stream or runtime claim follows from this module.
