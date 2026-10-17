# Minimal actual shared-edit row lineage route

No production file is changed by this review. The root owns the new row-lineage module.

## Indexed raw rows

Induct on `SourceCurrentAllocatedSharedEditGraph.RowsReads`. Generalize the current inventory, Ready, resident input edges, selected RowsSafe domains, and the current global memo Valid predicate. The cons graph retains the literal child scan, raw edge constructor, and suffix row scan. Split the requested output index into zero and successor.

Call `SourceCurrentAllocatedSharedEditEffects.children_effects` on the first child read. Use `facts.cached.edges` to derive available source children from the resident source edge. This returns a new inventory, the actual returned Ready, available result children, effects, and `first.globals.valid` at the child-return heap.

Move the source raw guard's field receipt with `FieldAvailable.grows first.effects.grows`. Call `SourceCurrentAllocatedSharedEditEffects.edge_physical` at the child-return state. Rewrite with the literal `rebuilt` pair from EditRows.cons. This supplies constructor Ready, Effects, output edge residency, and exact ordered children.

Use `MergedPhysicalGroupEdges.makeEdge_fields` at the same child-return heap with its actual Facts and available child values. Rewrite the literal constructor pair. This derives the full symbol and raw guard equality, not only effective equality classes or reference lists. `EditChildren.children_length` supplies source arity.

The suffix must receive the current memo Valid predicate. Start with `first.globals.valid`, then use `SourceQueryUnfoldMemo.valid_grows` with `first.ready.checked.semantic` and the raw constructor's `effects.keeps`. The edge constructor retains the complete global bundle but advances its reader heap. The private `heap_global` proof in AllocatedSharedEditEffects is the exact existing pattern; copy that short construction instead of invoking the private theorem.

Pass the suffix its actual constructor-return Ready, resident remaining source edges transported through both preceding effects, RowsSafe restricted to the tail, and this advanced Valid predicate. Do not reuse the original Valid proof at a later heap.

For index zero, expose the actual first child graph and ChildrenReads, constructor pair, and original suffix. For successor index, prepend the first row graph and read to the inductively returned prefix. Retain exact prefix/child/suffix shared states and global memo bundles. The output is an indexed source occurrence, with no injectivity claim.

The child graph already records selected node edits and unselected positions in order. Preserve that graph and its Reads. Do not identify a changed child with its original value. A separate indexed child theorem can recover a literal selected EditNode interval when a consumer needs it.

## Surviving ordinary node rows

Use `rows_effects` to derive the final raw row list's residency and its actual middle Ready. Apply `EqualityLeafProjectionPhysical.makeNode_edges` with middle Facts.coherent, Facts.linked, and this residency. Rewrite the literal node constructor pair.

A surviving output row is a member of `canonicalEdges (surviving rebuilt)`. `InternedProbeProvenance.canonicalEdges_member` and `List.mem_filter` recover membership in rebuilt. `List.mem_iff_getElem?` supplies a rebuilt index. Apply the indexed row theorem at that index. Canonicalization can reorder, remove dead rows, and deduplicate identities. Therefore the final normalized index need not equal the rebuilt/source index. `EqualityLeafProjectionPhysical.normalized_member` also derives the exact dead=false test if needed.

For growth into the final reader heap, compose the captured suffix row receipt's keeps/growth with the final makeNode constructor effects. The raw edge-return heap is not the final node heap. Every captured child or row input must use its actual interval effects before its availability or provenance moves to the final reader.

These claims apply to ordinary EditNode and actual EditRows. A recursive node first exposes Head, so a full recursive origin statement must include that separate origin branch. A leaf invokes the native query and needs native writer lineage. This review supplies no such result by assumption.

The allocated effects need only selected path domains. They retain open unselected siblings and arbitrary permitted recursive values. The older SourceEqualitySharedEditEffects whole-ClosedValues fragment is not needed for this route.
