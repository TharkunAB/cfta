# Secondary gate effects, endpoints, and actual head completion

Source main remains `525d722e`. The starting checkpoint is `516615d0`.
The checked proof checkpoint is `e7c08d35`, pushed to origin/formalize.
The [open ordinary-head note](notes-source-open-ordinary-head.md) records
the earlier one-unfolding result and the remaining general projection target.
This work derives effects and head completion from actual false gate traces.
General selected projection and whole-caller composition remain open.

## Semantic effects and reusable false certificates

`SourceSecondaryGateReplay` preserves SemanticReady and both constructor
histories through actual node, child, row, forest-path, and class traces.
Actual single unfolding supplies each intermediate cache and available
result. These theorems do not require CostHeap. They apply to either Boolean
answer and retain the source's ordered short circuit.

Every completed trace replays with the same Boolean and no constructor
effect in a heap that retains its final heap. Growth from the initial heap
alone is insufficient. Caller availability comes from history-preserving
effects or explicit available-value premises.

`false_edges_members` gives a false child certificate for every original
row of a false scan. `false_selected` retains the exact selected child.
`false_class_paths` gives a false certificate for every original class path
in each later retained heap. Thus callers can reuse these certificates after
seed rotation and intervening allocating operations. The membership proofs
retain original rows and paths. They do not assume identical traversal order.

`SourceSecondaryGateHeap` retains every physical edge-annotation predicate
through actual node, path, and class traces. Source stored unfolding copies
resident constraints. Replay effects derive intermediate availability and
readiness for ordered siblings. No final annotation heap is assumed.

## Original endpoint closedness

The gate unfolds open Mu values before it tests a node endpoint. A false
trace at node path [] therefore needs an unfolding retention proof.
`SourceSecondaryGateEndpointClosed.unfold_retains_free` derives retention
of every original external free name through the actual open Mu unfolding.
The proof uses exact prepared costs, actual execute_costs, and costs_free.
It also derives the returned gate Ready and result availability.

`endpoint_closed` then proves the original value closed from any completed
false node-endpoint trace. `of_done` starts from the actual completed worker.
These results keep the existing cost heap explicit in Ready. They do not
assume the input closed or use a semantic answer premise.
The forest root path [] remains different: its gate returns false without
reading any forest value. Exclude it from a false-path projection theorem.

## Actual repeated-Mu head completion

`SourceSecondaryGateHead.warm_head` derives a finite WarmHead certificate
from the actual false gate trace. Each recursive step records an actual
same-heap unfolding in the later caller cache. Its stopping values are empty,
ordinary, or closed. This certificate is derived from source execution.
It is not an assumed reader result or language assertion.

`collect_complete` follows the actual collect worklist for any initial
visited list. It retains visited-identity skips. Closed stopping values use
the earlier closed worklist completion theorem. `warm_nodeEdges_complete`
also retains the direct first-ordinary branch and the fallback that restarts
collect on the original Mu. Canonicalization retains resident returned rows.

`nodeEdges_complete` and `head_complete` derive actual reads and ordinary
head reconstruction in a later caller heap that retains the gate's final
heap. They derive both histories, SemanticReady, availability, and an ordinary
result. `head_verified` transports those properties to any completed actual
Head receipt by exact uniqueness. No whole-value closedness or cost heap is
required for these head completion results. They do not establish closed
children of the exposed head.

## Independent language of actual heads

`SourceSecondaryGateHeadLanguage.head_exact` proves exact independent
language for every actual Head receipt after a false gate. It uses initial
and caller SemanticReady and availability, plus growth from the gate's final
heap to the caller heap. No cost heap, closed-input premise, preparation,
acyclicity assumption, or semantic-output oracle is required.

The forward inclusion derives a constructor origin for each accepted term
in a future cache. This future comes from actual closed reads at stopping
values. Replay retains the parent's actual read there. A new open-root
fixed-cache coverage theorem supplies row membership after actual identity
skips and canonicalization. Residency comes from the traversal certificate
and actual edge origins. No future language premise is supplied.

The reverse inclusion follows actual WarmHead worklist steps. Each emitted
edge has the original independent language. Actual unfolding supplies exact
language equality at each prefix. Closed stopping values use existing
closed-read soundness. `head_included` retains the forward result separately.

## Physical annotations of actual heads

`SourceSecondaryGateHeadHeap.warm_head_heap` preserves every initial physical
edge-annotation predicate through an actual Head receipt. A private induction
follows the bounded collect operation for any visited list and outcome.
It retains actual identity skips, same-heap Mu unfolds, and the source
fallback that restarts from the original Mu. Closed stopping values use
the existing closed annotation theorem. Actual makeNode preserves the
returned heap. `head_heap` derives this result from the false gate trace.
No cost heap, original closedness, or final annotation heap is assumed.

## Remaining obligations

Derive finite selected projection from a false nonempty forest-path trace.
Use one fixed anchor heap G, the completed gate heap. A candidate support
invariant says a value is closed, or is available in G with an effect-free
false node certificate at its remaining path. SemanticReady G supports
replay. CostHeap G is needed only to close an endpoint certificate at [].
Original gate Ready can retain that cost heap to G. Later native heaps
do not need the cost heap for this argument.

The next lemma must transfer this support to each selected child of each
actual exposed row. Recover raw row membership through makeNode and
canonicalization. Use actual nodeEdges origins and epsilon reachability.
Closed successors stay closed. A certified open successor must follow
the recorded Mu unfolding. Ordinary false scans supply each selected
child certificate through false_edges_members and false_selected. Retain
row boundaries and child positions; makeNode_children alone loses them.
This plan is not yet a checked theorem.

Then induct on path length. Reuse the existing closed projection theorem
for closed support and actual head completion for recursive support.
Derive finite execution, accepted-subtree inclusion, and annotation retention.
Do not assume whole-original-forest or whole-recursive-head closedness.

Then instantiate the seeded refused-class query and compose primary class
partition, secondary scan, query, fallback, and caller. Keep both gate modes,
all three memo families, lazy row demand, original child forcing, checked
native transfer, machine bounds/identities, and general completion separate.
Waiting counts, template exclusion, broader API/runtime bridges, recursive
generators, and all distinct exact Sized contracts remain in the full scope.

## Validation and preservation

The pinned full audit passes 2,037 jobs and 51,930 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. The old unused-input
warning remains. No new warning, admission, or axiom occurs.
Log: `/tmp/mcfta-secondary-gate-audit-20261015.log`.

All prior Lean definitions remain byte-identical except four additive Audit
imports. All four Haskell package trees match `516615d0`; their unchanged
checks were not repeated. All prior proofs, repros, marked drafts, external
drafts, stashes, and other worktrees remain. The new failed heap draft
`/tmp/mcfta-secondary-gate-heap-draft-20261015.lean` is marked and preserved.
It is not part of the checked proof tree.

Start: `/tmp/mcfta-open-head-checkpoint-20261015-1910/` (2,696 files).
Closing: `/tmp/mcfta-secondary-gate-checkpoint-20261015-1936/` (2,703 files).
Script: `/tmp/mcfta-preserve-secondary-gate-20261015.py`.
Weekly allowance is 86%. Full scope remains active.
