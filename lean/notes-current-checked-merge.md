# Current checked merge and selected target operands

Source main is `8f85ddb6`. The preceding published proof checkpoint is
`b7510ec5`. Proof commits are `784b2168`, `6938c72f`, and `4d9ea213`.
No Haskell implementation or test file changes.

## Actual allocation graph

`SourceCurrentAllocatedMergeGraph` retains the ordered completed merge
program and its warm result table. The new `topRow` instruction first demands
the canonical empty equality field, then interns the raw Top edge.
Only the large-group program uses this instruction. Small rows retain their
original fields. Completed hits skip the body and retain the complete state.
The final node can discard an edge with an empty child after its allocation.

Erasure removes only equality-operation effects. It preserves literal
outputs, constructor heaps, and merge tables. `Run.graph` and `Call.graph`
derive the old heap graph from the same new allocated graph.
`run_lift` and `call_lift` construct allocated execution from an actual erased
run and arbitrary initial operations. They assume no future result or
future operation invariant. Existing constructive heap-only completion then
derives the new allocated completion.

This is a completed sequential projection. HashMap group order, earlier
pending memo publication, concurrent forcing, and GHC demand adequacy remain
adapters. The graph does not establish eager evaluation of source children.

## Dynamic physical fields

`SourceCurrentAllocatedMergePhysical.SafeCode` checks raw constructor fields
in the current operation cache. Operation growth transports those checks.
The source body derives its small-row fields from actual resident edges.
The reached `topRow` derives Top availability from `empty_field`, after its
canonical allocation. Mutual instruction and request induction retains the
semantic heap, costs, loaded fields, operation validity, warm merge Stored
records, and available returned winners.

`Call.verified` derives these effects for the same actual call.
`call_complete` constructs the call from initial Ready, Stored, and available
input. It needs no initial Top field and no closed whole forest.
Closed input derives closed output. Open input uses the source direct return.

## Current checked state and language

`SourceCurrentAllocatedMerge` advances the full checked state with that
physical return. Both native request tables and the domain cache remain
identical. Equality operations can grow. Full Ready, machine Extension, and
the same concrete Inventory.At follow from the actual effects.
The next native query admits a generated merged operand when it is requested.
No generated model or semantic callback is supplied to merge completion.

Warm merge Stored and semantic CacheCovers are initial invariants.
CacheCovers is uniform over ambient environments. Empty tables derive both
invariants; this does not claim that a production global table is reset.
The derived old graph supplies language coverage and exact global receipts.

The source structural comparison tests `edgeConstraint wide == noConstraint`
at `Interned/Operations.hs:672`. `literalClear` uses the corresponding raw
equality with Top. Independent PCS Top truth derives its semantic law.
The broader normalized `SourceMemoGate.plain` test is different.
`normalized_clear_boundary` proves the difference for an empty And guard.
The source enumeration gate uses normalized equalities and residual guards;
its separate predicate remains appropriate to that different source test.
This distinction is a proof adapter correction, not a Haskell behavior fix.

The selection primitive still has a pure clear callback. Comparing with the
source `noConstraint` CAF can itself demand its empty equality allocation.
The new final-row allocation does not prove the source allocation trace
inside selection or its lazy interleaving. That runtime adapter remains open.

## Selected target operands

`SourceCurrentConjunctionTargetProjection` constructs the actual projection
from resident values and the selected ForestClosed domain. It retains current
operations, native tables, inventory At, and global receipts. Other original
siblings can stay open. Proper paths preserve accepted selected subterms.
The root projection has exact union language. Proper projection has no
general converse, because ancestor guards are discarded.

`SourceCurrentAllocatedMergeOperand.complete` passes the exact projection
return into the allocated merge. It derives a closed available result,
retained original values, physical effects, same native and domain tables,
warm merge-table extension, inventory At, and final global validity.
Its receipt keeps both intermediate graphs and global bundles.
`of_required` obtains the selected domain from the current required receipt.
Merging is an over-approximation. The operand preserves selected accepted
subterms without claiming exact language equality.

The independent `operand_then_query` kernel constructs this operand and the
next generated native query. The query derives its expanded inventory and
result language from the actual operand return and reached WordRanges.
It needs no supplied next model, admission oracle, or future result law.

## Validation and next target

Pinned Lean 4.34.1 passes the full Audit with 2342 jobs and 56610 theorem
dependency checks. Only standard foundations and the preexisting unused-input
warning occur. Public probes, integration kernels, source copies, independent
reviews, and logs are in `restart-evidence/20261016-checked-merge/`.
The preservation verifier checks all 3792 starting files and all 2336 older
non-Audit proof sources. All older source bytes remain.

Next port the first-seeded target fold, using the checked operand and actual
next generated query. Then port class-local slots, target forcing, leaf
narrowing, and the compiled class edit fold. Keep merge and native tables
warm. Capture the forest returned by the preceding class tail.
Final empty propagation, inherited constraints, the general constrained
outer caller, broader frontend and runtime-family adapters, and all remaining
full-library obligations stay active. The full goal is not complete.
