# Selected observation spine contract audit

Read-only design audit, 2026-10-19 01:32 CEST. No Lean job or production edit was made.
This note specifies contract checks. It does not assert a new theorem.

## Required causal connection

An event somewhere in an edit call does not explain every later read of that call's result.
The witness must follow the selected projection through the actual edit graph.
Index the derivation by that graph, the requested path, the actual projection, its returned value and heap, the subsequent read, and the selected full row.
Keep any intervening `Keeps` from the projection return to the read entry explicit.

A suitable observation shape is:

```text
Project path value projectBefore projected projectAfter
Keeps projectAfter readBefore
Read projected readBefore rows readAfter
row ∈ rows
```

These are actual equations or graph receipts. They are not an assumed source or result relation.
The event derivation must connect to this same observation.
It must not existentially choose a different later projection or row.

## Constructors that prevent unrelated events

**Leaf cut.** Retain the exact `NodeReads.leaf` receipt, its target force, its actual native query, and its returned value.
The residual observation must start from that returned value.
The residual path can be nonempty. Do not replace it by physical row membership in the native result.

**Head cut.** Retain the exact `EditNode.recursive` constructor, its `HeadReads`, its returned exposed value, and the recursive body edit with `NodeReads`.
The remaining observation starts from the body edit's returned value.
The Head event therefore precedes the real body edit.
Do not assert an observation of the unchanged exposed value when the body changes it.

**Ordinary child lift.** Retain the selected canonical output row, its raw rebuilt row, the corresponding original raw row, the selected child, its exact `Slice`, and the recursively derived observation of that child.
The recursive witness must use that same child and the remaining path.
The prefix and suffix child calls retain their real states and memo bundles.

**Ordinary root.** At an empty path, an ordinary output row already has its original full row fields.
An event in an unrelated child does not supply the root-row witness.
Use the exact ordinary survivor source instead.

**Recursive lift.** A nested event stays inside the actual recursive body graph.
An arbitrary event in the enclosing graph is not a substitute for this lift.

## Three distinct row positions

Keep these positions separate:

1. The result position of `ProjectRows`. Missing selected child slots do not add a result.
2. The canonical row position in `nodeEdges` of the edited ordinary value.
3. The raw rebuilt row position, which aligns with the original row scan.

`ProjectionIndexedOrigins.rows_indexed` connects the first position to the second.
`SharedEditRowLineage.node_survivor` connects the canonical survivor to the third position.
`SharedEditChildLineage.Slice` then connects the physical child position to its actual edit call.
None of these positions can be replaced by another without its lookup receipt.
The signed projection lookup rejects negative indices.
Derive the natural child lookup from the actual successful signed lookup. Do not assume it.

## Reuse before adding helpers

`ClassFoldRowOrigins.rebuild` already retains the original raw index, raw rebuilt index, exact `makeEdge`, full symbol and guard, ordered children, row liveness, actual row prefix, child reads, readiness, histories, growth, and all child slices.
`SharedEditChildLineage.row_child` is useful when a selected edit is already known, but its conclusion omits some canonical and suffix detail.
Do not add a second whole-row receipt that repeats `Rebuild`.

The small extra bookkeeping lemma, if needed, is an indexed survivor inverse for an actual `Union` from semantic readiness, cost heap, and available operands.
It should return the selected operand index, earlier and later `ReadAll`, the exact selected `Read`, its full selected row, and the final `makeNode` receipt.
`ProjectionIndexedOrigins.union_row` has this shape but also asks for closed operands.
The new spine must not add global closedness only to use that helper.
`SourceEqualityProjectionCosts.read_effects`, `readAll_effects`, and `union_effects` support the actual successful schedule with open operands.
They supply the semantic and resident facts needed for the same survivor inverse.

The private `RequiredProjectionOrigins.ordinary_read` already gives the other small fact: an actual read of an ordinary value returns its literal `nodeEdges`.
The private `union_accepted` proof already shows how to consume an actual selected union row without a closed-operand premise.

## Physical support and history

Use `AllocatedSharedEditEffects.node_effects`, `children_effects`, and `rows_effects` at actual captured prefixes.
They derive returned readiness, availability, `Keeps`, and global memo effects.
`ParentNativeHistory.edit_node`, `edit_children`, and `edit_rows` derive native writer history from the actual read graphs.
`Slice` and `Rebuild` expose the exact prefix histories needed for a selected child.
No future enclosing edit or class return is needed beyond the completed graph under analysis.

`Grows` retains old records. It does not supply causal guard certificates for new Mu records.
Use the actual native, lower, projection, and read guard-preservation producers to carry `ConstrainedCapGuardHeap.Heap Plain` forward.
If the contract instead takes that heap at a later reader, old-record retention can restrict it to earlier captured heaps. State that direction explicitly.
Do not infer the final guard heap from growth alone.

`ConstrainedCapProjectionGuard.read`, `head`, `union`, and `node` preserve the causal guard heap through their actual successful operations.
The initial semantic, cost, and availability premises remain necessary.
This causal heap does not assert that every raw guard is plain.
The original gate and the Required origin supply the local plain-region argument on untouched branches.
They do not supply a false gate on the edited value or plainness of a native event.

`History.advance` changes the physical heap while retaining the actual native tables.
It therefore supports forward writer lookup at the read's final heap.
It does not derive current physical `Good`; obtain that from the actual physical effects.
Do not use an origin at the read's final heap as an origin at its earlier entry heap without a separate valid transport theorem.

## Existing native endpoint boundary

`MergedFreshOrdinaryExposureOrigins.nodeEdges_origins` derives a complete epsilon origin at every extension of the actual read return.
`NativeOriginExposure.returned` and `request` consume that origin and recover the captured native writer and any retained-Mu unfolding.
They already solve this endpoint when the residual observation is a complete read of the native result.

A nonempty residual path is different.
Its row can be below an ordinary child and need not be an epsilon origin of the whole native result.
Keep the residual path and its actual observation in the event receipt.
When the native branch is ordinary, `NativeNodeRowLineage` can supply the actual selected row and ordered child query.
Do not call the epsilon endpoint on a path-descendant row without first deriving the required origin.

## Contract checks before freeze

- An event in one sibling must not discharge an observation of an unselected different sibling.
- A missing child position must not shift the source row index to the projection result position.
- Canonical deduplication must retain an actual raw preimage and its selected child call.
- A Head cut must retain a changed body return and the real observation of that return.
- A nonempty leaf residual path must remain visible.
- Later class edits must remain an explicit continuation. They cannot be replaced by the unchanged event value.
- The original-source branch must not assert unchanged children or `All₂ Required Origin` across native edits.
- No global rank, all-source simulation, termination, or Haskell correspondence follows from this spine theorem.

## Inspected source pins

| Source | SHA256 |
|---|---|
| SourceCurrentAllocatedSharedEditGraph | `18dcc2fa70e0eb95731fd19607e730664ba031949099de52e9ab1949f623d629` |
| SourceCurrentClassFoldRowOrigins | `d57ecf4371ed53c17ca0f64feb30994764612cac51483eb36a207a0f5fa4faab` |
| SourceCurrentSharedEditChildLineage | `822fd3d96648267efd014547599b94530b9ce98e6d3c615831a94f8c2bfca4d0` |
| SourceCurrentSharedEditRowLineage | `4b02b1748d11f0e5eb19cdd1f4da1f7dd44cfb7164a77c509b560b01d347d28c` |
| SourceCurrentProjectionIndexedOrigins | `143b94d6471f9baebd754012e3e5b4d029ac74a52d1bfd77323c3fe3b41f352a` |
| SourceEqualityProjectionCosts | `56b09c5ba2da1aabe7249b1e51cda3df7891ae9cc42d5585b17b54c70bf25bc4` |
| SourceCurrentConstrainedCapProjectionGuard | `29724342b76fc72b75800ec9760e583a78f9b2ae182d545b991add271aa6c61b` |
| SourceCurrentNativeEdgeWriterGrowth | `3a2faba33207e1518bb9ceeed0c4b0bd2d50e09951de575077c4fd573f22ae14` |
| SourceCurrentParentNativeHistory | `3c88c79958b914299db33ca5875f7795c3e48da99febb56eb6c17377ef1bac64` |
| SourceCurrentRequiredProjectionOrigins | `ebf430e8c217d2f6083ea23447ae56df5f4ede03a67341d407e002eca2abdc67` |
| SourceCurrentNativeOriginExposure | `20ecd0f0f4ae76264f1cc59f44aee95181c095de0e65f5dc4ee8ff749b8bf046` |
| SourceCurrentNativeNodeRowLineage | `a079b1a2040b24b0180f0063319f67d7f27c8b2fe70c5a349f7825f984ec0064` |
