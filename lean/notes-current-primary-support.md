# Projection support from false current primary gates

Source main is `e16f3b50`. Equality worker bodies match `2ca1644c`.
`SourceCurrentPrimaryProjectionSupport` uses actual enabled-primary false
node, path, and class traces at their exact returned heaps.

## Structural and semantic results

`node_false`, `path_false`, and `class_false` derive current secondary
certificates with the same input, output heap, unfolding equations, and
ordered child reads. A false primary endpoint implies the free-list test
is false. The primary constrained-Mu branch cannot produce false. The
remaining branches retain their literal source operations.

This conversion constructs a structural certificate. It does not execute
another gate or infer an additional global memo call.

`node_support`, `path_support`, and `class_support` derive projection
support at the actual primary final heap. Initial semantic readiness,
CostHeap, and available original inputs derive final semantic readiness,
gate readiness, heap retention, and original input availability. Path and
class wrappers require proper original paths. No accepted candidate or
whole-original-forest closedness premise is supplied.

`head_selected_support` follows an actual later Head receipt. It derives
shorter support for every selected child of every actual exposed edge.
The later caller must retain the anchor heap and original availability.
It needs no later CostHeap. Unrelated original siblings can remain open.

## Remaining fallback work

Support through requireAll, rebuilt class forests, shared targets, and edits
remains open. Proper paths still come from actual original class entry.
These results do not initialize memos or establish full fallback completion.
Keep merge/subsumes global reads, separate merge memo, costs, fields, checked
native transfer, runtime execution, and general completion as separate tasks.

## Validation

The focused pinned build passes 1,045 jobs. All seven public axiom probes
pass. The aggregate audit passes 2,114 jobs and 52,819 dependency checks.
Only the three permitted Lean foundations occur. No new warning occurs.
Evidence: `/tmp/mcfta-normal-form-primary-*`.
