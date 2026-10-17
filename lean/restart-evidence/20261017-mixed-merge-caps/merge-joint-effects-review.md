# Actual Merge guard and joint-store effects

Reviewed on 2026-10-17 at 05:38 CEST. Both production modules are additive. No earlier proof or Haskell file changed.

## Produced guard heap

`SourceCurrentConstrainedCapMergeGuardEffects.lean:22` proves guard-heap retention for the actual repaired stored unfolding. The Mu branch invokes `GuardNative.execute_heap` on the actual stored body and the literal outer-reference replacement. The replacement is available because it is the original available Mu. This is not a global hereditary guard premise.

The private collection proof at line 38 follows the exact fuel, visited set, and worklist. Ordinary rows prepend without changing the heap. Union members retain their actual input availability. A demanded Mu executes its actual unfolding. The returned guard heap and semantic readiness pass to the shorter worklist. This proof covers the actual stopping heap, including exhaustion and unresolved branches. The nodeEdges proof at line 82 handles both the direct unfolded ordinary head and the fallback on the original Mu at the returned heap.

The public Effect at line 119 contains physical Keeps, SemanticReady, CostHeap, and a PRODUCED implication from the initial guard heap to the returned guard heap. The actual comparison induction at line 234 discharges each smaller callback by fuel induction. Ordered child, row-cover, anyAccepts, retention, and selection stages thread the actual intermediate heaps. None requires Annotated or Cap on the compared operands. The helper callbacks are private induction interfaces. They are not public future-result assumptions.

## Actual memo-aware Merge

`SourceCurrentConstrainedCapMergeJointEffects.lean:20` privately checks that source constructor instructions make no new Mu record. This property is proved for the literal node, edge, union, and ordinaryUnion work emitted by every source body. It is not inferred for arbitrary Work.

The mutual actual Run/Call proof at line 83 retains the initial guard heap. The selection case invokes the new actual selection producer. A request uses the smaller actual Call proof. A bind passes the preceding actual heap into its continuation. A hit executes no body. A miss uses its smaller actual body Run and then retains its produced heap through the actual remember and keep-first winner lookup. It needs no annotation or cap property of the Merge input. In particular, the result of a losing candidate does not justify an earlier winner. The guard heap concerns actual constructor records and is already valid in the body's returned heap.

Public `call_heap` at line 135 verifies the supplied actual memo-aware Call. Public `merge` at line 154 verifies the SAME allocated Merge graph. It uses the existing physical erasure to obtain the exact constructor heap, and the allocated physical proof to obtain the full equality-operation state. It derives the returned guard heap from the actual call. It then uses CurrentNative.advance to retain and rebase joint laws and captured origins at the literal current heap. Both native tables and the domain cache are unchanged by this physical advance. InventoryState.At.advance retains the earlier fixed semantic input model on the same checked state.

The initial readiness, physical Merge store, semantic inventory, and current causal joint stores remain explicit. No future guard heap, desired output law, current body completion, or callback completion is an input to these producers. The supplied graph is a verification input. These modules do not themselves construct arbitrary Merge graphs.

## Integration evidence

`merge-joint-effects-kernels.lean` has two imported signature and axiom pairs.

1. `recursive_comparison` constructs its own finite repaired comparison from initial semantic readiness and actual available closed operands. The wide operand is a Mu. The narrow operand has a nonplain ordinary row. The kernel derives the returned guard heap and proves that this ordinary operand is not hereditary. No completed comparison or future heap is supplied.
2. `serial_generated_merge` constructs two actual allocated source Merge receipts. The second call uses the first call's produced result, returned heap, populated Merge memo, equality-operation state, and global memo. Both returns retain CurrentNative.At. The final semantic inventory is retained. The kernel takes initial warm readiness and causal invariants; it does not construct the initial source heap or prove a cold bootstrap.

The two production strict checks and all 11 public pairs are clean. Both integration pairs are clean. The allowed axioms are propext, Classical.choice, and Quot.sound. Earlier failed source snapshots and raw diagnostics remain present. The canonical logs replay only the existing InternedFreshOrdinaryClosedCompletion.lean:24 unused inputs warning.

## Scope

This closes actual comparison and Merge effect retention needed before a generated checked query. It does not prove a mixed Merge output cap; that is the separate actual cap producer in this checkpoint. It does not establish cumulative serial numeric resources, broader editor gate support, general outer recursive reduction termination, lazy memo publication, or GHC forcing correspondence.
