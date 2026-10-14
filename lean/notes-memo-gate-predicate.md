# Complete memo gate graphs and the concrete source predicate

Current update (2026-10-15 01:52 CEST): `f3d27627`, `a93d1b35`, and `d0d8ac1f`
complete the ordered class filter with both memo tables. Each class occurrence
retains its exact intermediate caches. Derived gate replay connects all
decisions to the pure selected-class operation in the retained final cache.
Read [the current note](notes-ordered-class-selection.md). Earlier next
targets below retain their historical context.

Current update (2026-10-15 01:40 CEST): `0f5f465f`, `348e5adc`, and `9abb1aff`
complete exact physical descendant checks for the actual visited source fold
and carry both actual memo tables through complete ordered gate graphs.
Read [the current proof note](notes-source-crush-both-memos.md). Its next
target is the complete ordered local-class filter. Earlier next targets below
retain their historical context.

Updated: 2026-10-15 01:23 CEST.
Proofs: `c087a4ed`, `13b10b57`, and `3602e821`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
Publish completed checkpoints on `formalize`.

## Unfolding memo composition

`InternedFreshOrdinaryMemoGateTrace` defines node, child, and ordered edge
graphs that pass the unfolding memo and constructor cache together.
Each Mu step contains the actual memo runner equation and its exact repaired
constructor readback. Each false edge passes both returned caches onward.
Each true edge omits the unvisited suffix.

`InternedFreshOrdinaryMemoGateLift.lift_node` derives every readback through
the actual coherent memo runner. Its mutual graph induction covers arbitrary
nested Mu, original child order, canonical hits and misses, and discarded
suffixes. Every returned cache retains semantic contexts, depth heaps,
payload coverage, weighted heaps, memo coherence, and both growth histories.
No whole-trace memo observation law is supplied.

`InternedFreshOrdinaryMemoGateClasses` adds path and complete class graphs.
`lift_class` retains both caches across original path order. `class_trace_iff`
proves equivalence with the complete source class graph in a ready cache and
coherent initial memo. `memo_independent` proves that certified class traces
have the same Boolean and final constructor cache, even with different
starting unfolding memos. It does not assert equality of the returned memo
tables. `source_nodes` and `source_classes` derive initial caches, empty memo
coherence, complete graphs, and exact finite source readback from original
construction. No completed construction or gate call is supplied.

The graphs are logical execution graphs with actual memo call equations.
The existing fuel worker supplies exact finite constructor-cache readback.
This work does not add a separate extracted executable memo gate backend.

## Concrete source predicate execution

`InternedSourceCrush` follows `Data.CFTA.Interned.Operations.crush` at the
Boolean `All` monoid used by `Enumeration.unconstrained`. It skips empty
records and bare references. It marks ordinary, union, and Mu identities
before visiting their actual source children. Ordinary edge children retain
their original flattened order. Mu visits only the stored body. Neither
probe participates. No recursive record is unfolded.

The complete worker is structurally recursive. It has no supplied gate fuel.
`visit_seen` proves exact skip behavior. The mutual visited-growth laws
retain every earlier identity. `InternedSourceCrushInventory` proves that
the visited set stays distinct and below the actual node counter on coherent
available records. Its final length is at most `state.nodes.next`.
This bounds distinct visited identities. It is not a machine runtime bound.

`SourceMemoGate.plain` uses the existing normalized equality and residual
source test. `plain_eq` identifies it with the checked cyclic edge predicate.
`unconstrained` is the actual visited-node Boolean traversal with that local
test. `nodes` and `classes` install it in the complete source-derived memo
graphs. No whole-node predicate or predicate correspondence law is supplied.

The scalar normalization wrapper retains the existing noncomputable logical
source model. The new wrapper is not an executable Lean normalization backend.
The visited traversal itself is a structurally recursive function.

`SourceUnconstrainedMemo` models the separate predicate memo. Its entries
retain complete immutable inputs and exact concrete Booleans. `run_exact`
proves both hit and miss behavior by canonical record coherence.
`grows` retains all saved reads after actual constructor and reservation
growth. The predicate memo does not change the constructor cache.

## Remaining semantic and composition work

The visited inventory and concrete source read do not yet prove the full
semantic characterization of the fold. Prove that its Boolean is true exactly
when every ordinary edge reached through stored bodies, ordinary children,
and union members passes `plain`. Include shared identities, arbitrary open
nested Mu, and root unions. Bare references stop. Do not follow them by
unfolding. Use actual canonical record coherence for repeated identities.
Do not assume a whole-fold correctness law or restrict all unrelated cached
edges to be unconstrained.

Then carry `SourceUnconstrainedMemo` through complete gate graphs alongside
the unfolding memo. The predicate call law is already proved. Reuse it and
its growth invariant rather than supplying a pure-read observation premise.

Exact Sized reference, optimized, and solver-decided contracts remain.
The optimized interned core remains. Native memo containers, lazy scheduling,
primitive resources, external solvers, and verified Haskell extraction retain
their stated limits. No production Haskell code or dependency changed.

## Validation and preservation

The pinned Lean 4.34.1 audit passes 1,598 jobs and checks 44,916 theorem
dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`.
Only the old unused `inputs` warning remains. Log:
`/tmp/mcfta-memo-composition-source-predicate-20261015-audit.log`.
All earlier proof bytes are unchanged except for seven audit imports.
All counterexamples and marked drafts remain. Snapshot:
`/tmp/mcfta-memo-gate-predicate-checkpoint-20261015-0123/`.
It saves all 1,982 Lean-tree files and four root documents.
