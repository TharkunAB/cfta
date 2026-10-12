# Physical normalization for projected leaf edits

`EqualityLeafProjectionPhysical` derives exact ordinary-node readback from
the existing coherent edge and node caches. `makeNode_edges` returns the
complete canonical surviving edge list, including a cache hit. It does not
infer payload equality from identity alone without residency.

`mapped_normalization` proves that child mapping and an optional row filter
can run on the retained original occurrences or on the actual normalized
edge list. Both produce the same complete `makeNode` computation. The proof
uses `InternedNodeSetCongruence.makeNode_same_members`. It requires each mapped
row to be resident and requires a dead original row to remain dead.

`rebuild_dead` derives the latter property from the actual `makeEdge` return
fields and an empty-preserving child map. `rebuild_fields` proves that the
rebuilt ancestor retains its symbol, complete guard, and child arity. These
properties apply to actual ordered child reference lists and canonical
payload readback, not only to a semantic row interpretation.

`EqualityLeafProjectionRebuild` executes the finite parent-edge requests in
occurrence order. `rebuildMany_completed` derives final coherence, the exact
ordered result list, output residency, and allocation-free replay of every
request in the final cache. `completed_readback` uses this execution to
remove the supplied output-residency premise. Its edit and required-path
corollaries use all rows and the literal original-arity filter, respectively.

These theorems establish the physical parent-constructor normalization part
of the projected-leaf adapter. The child transformation is still a supplied
function of child position and complete child record. Recursive edit and
required-path execution must provide that transformation and its empty-node
law. The proof compares final parent requests in the common resulting cache.
It does not claim that executing retained duplicate or dead occurrence rows
has the same allocation trace as visiting only normalized source rows.
