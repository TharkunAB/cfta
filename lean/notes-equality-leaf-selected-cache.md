# Complete selected-row preparation

`EqualityLeafProjectionRequireSyntax` proves that a requirement fitting
arity zero contains only root paths. It leaves the whole original occurrence
syntax unchanged. This supplies the exact counterpart of the source worker's
direct-return branch, including original duplicate ancestor rows.

`EqualityLeafProjectionSelectedCache` refines parent preparation to build
only selected original rows. The normalization proof leaves each unselected
original edge record unchanged. Actual earlier-to-later cache growth retains
those records. No discarded child request or discarded rebuilt edge is needed.

This distinction is required for full payload availability. The earlier
`ParentCache.prepare_correct` establishes coherence and record growth only.
Its proof-only reconstruction of unselected rows can use child readbacks
whose returned records were never installed in the retained cache. That
construction must not be used to infer the stronger `Cached` invariant.

`EqualityLeafProjectionPreparationAvailability.prepare_facts` derives full
coherence, stored child availability, and node-to-edge links for selected-only
preparation. It executes every selected original child request. The final
child cache replays each request, so its mapped child result is available.
Rebuilding only those selected rows then preserves the complete payload facts.
The source worker availability theorems discharge the local request condition.

The optional empty fallback is available even outside the ordinary fragment.
This availability fact does not turn a failed worker into a successful one.
The compiled ordinary-input theorem separately rules out those failures in
the represented source fragment.
