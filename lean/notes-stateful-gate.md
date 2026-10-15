# Ordered source gate execution and coherent unfolding memo

Current source update: main `24a710a3`, merged at `6a02619c`, adds a
constrained-descendant check at ordinary path endpoints. The pure current
policy and actual-record finite checks are proved in `3eed507c`. The older
stateful/memo selection pipeline below retains its earlier policy. Caller-cycle
witnesses remain historical; the preserved cold Haskell fixture now completes.
Read [the current source comparison](notes-main-24a710a3.md). General caller
termination and the new descendant memo remain open.

Current update (2026-10-15 02:13 CEST): `ae6a0141`, `ac7c1eaf`, `97f987a1`,
and `a84343e3` derive the physical class sort, source prechecks, actual
array-normalization readback, and complete guarded selection. The next
requireAll target has a checked closed raw self-binder stutter and Haskell
reproduction. Read [the current note](notes-physical-class-order-entry.md).
Earlier next targets below retain their historical context.

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

Current update: `c087a4ed`, `13b10b57`, and `3602e821` complete unfolding-memo
composition through the gate graphs and install the concrete visited-node
source predicate. Read [the current note](notes-memo-gate-predicate.md).
It states the remaining visited-fold semantics and predicate memo composition.
The sections below retain the earlier checkpoint.

Updated: 2026-10-15 01:06 CEST.
Proofs: `ec56843a`, `512a386d`, and `8b5ec04e`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
Publish completed checkpoints on `formalize`.

## Actual ordered cache effects

`InternedFreshOrdinaryStatefulGate` follows
`Data.CFTA.Equality.Operations.nodeMeetsConstrainedMu`. References and stored
unions return true before metadata shortcuts. Finite ordinary records return
false. An open unconstrained Mu follows actual repaired unfolding at the same
path. An ordinary edge consumes one child index. Missing children return false.
`meets` starts below the constrained edge's root.

`anyKnown` threads actual returned constructor caches through original order.
A true result stops the scan. A completed false query passes its cache to the
next edge or class path. Missing gate fuel returns `done none`. A pending
constructor request remains `pending key`. Neither is a false gate decision.

The fuel stability theorems retain the exact Boolean and final cache. More
fuel cannot add hidden work after a completed short circuit.

`InternedFreshOrdinaryStatefulGateCompletion` uses the already proved strict
actual open-Mu rank. Path length decreases for child traversal. Rank decreases
for same-path Mu unfolding. Its finite scan theorem follows each returned
cache. Both growth histories keep the next sibling's original inputs available.
`node_complete`, `meets_complete`, and `class_complete` derive finite Boolean
evaluation. Every returned certified cache retains context, depth heap,
payload coverage, weighted heap, and available records. No successful gate
call, shallow body, or sibling restart in the original cache is assumed.

## Separate logical source graph

`InternedFreshOrdinaryStatefulGateTrace` defines logical node, child, and
edge graphs. They have no gate fuel. Each Mu step contains the exact actual
unfolding equation. Each false edge passes its exact intermediate cache to
the next edge. Each true edge omits the unvisited suffix.

`InternedFreshOrdinaryStatefulGateGraph.node_trace_iff` proves both
graph/execution directions. The reverse proof uses the mutual graph recursor.
It constructs sufficient finite fuel for the complete ordered trace.
`node_trace_unique` proves uniqueness of the Boolean and final cache.

`InternedFreshOrdinaryStatefulGateClasses` supplies path and complete class
graphs. `class_trace_iff` and `class_trace_unique` give the same exact laws.
`cached_class_trace` derives a logical graph and stable finite executable
trace with all returned cache invariants. `source_node_trace` derives original
construction completion and finite traces for every finite path.
`source_edge_classes` derives class traces for every original outgoing edge.
Neither source theorem assumes a completed construction or gate call.

This applies the function/graph correspondence and functionality method
discussed in [the Lava note](notes-lava.md). It remains a Lean source model.
It does not establish a new Haskell translator or extraction theorem.

## Outer-unfold memo

The source `Data.CFTA.Interned.Operations.unfoldOuterRec` uses a separate
memo table. `InternedFreshOrdinaryUnfoldMemo` models its canonical lookup,
miss execution, and result insertion. Entries retain the complete immutable
input and output. `Correct` derives exact saved-result readback in the current
constructor cache. Actual canonical identity and coherence make a hit select
the complete queried record.

`empty_correct` derives the initial invariant. `grows` retains every old
entry after constructor and reservation growth. `run_complete` proves each
actual hit or miss returns exactly the repaired unfolding value and constructor
cache, plus a coherent returned memo and both histories. A miss installs a
new coherent entry. The proof reuses the existing general stored unfolding
replay theorem in `MergedFreshOrdinaryColdReplay`.

The current gate worker still calls repaired unfolding directly. The memo
runner is proved separately for one actual query. Next carry this runner and
its invariant through complete ordered node, edge, path, and class graphs.
Use its exact readback, not an assumed memo observation law.

The current constraint predicate is an arbitrary pure read. Next derive
`Enumeration.unconstrained` from `crush` and the actual edge constraint test.
Its source Mu traversal visits only the body. It does not visit either probe.
Canonical visited identities must retain exact complete records.

The optimized interned core and exact Sized contracts remain unchanged.
Native containers, memo storage primitives, lazy scheduling, machine resources,
external solver behavior, and verified Haskell extraction retain their stated
limits. No production Haskell code or dependency changed.

## Validation and preservation

The pinned Lean 4.34.1 audit passes 1,591 jobs and checks 44,835 theorem
dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`.
Only the old unused `inputs` warning remains. Log:
`/tmp/mcfta-stateful-gate-memo-20261015-audit.log`.
All earlier proof bytes are unchanged except for six audit imports.
Every counterexample and marked draft remains. Snapshot:
`/tmp/mcfta-stateful-gate-checkpoint-20261015-0106/`.
It saves all 1,974 Lean-tree files and four root documents.
