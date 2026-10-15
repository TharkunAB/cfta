# Executable merge and physical memo-aware class entry

Source main is `4101746a`, merged at `0fca52f8`.
This increment retains the earlier constructor and equality proofs.
It keeps the optimized interned core.

## Executable merge

`SourceCurrentMemoMergeWorker` executes the actual instruction and call graph.
Its result contains the returned value, heap, and completed merge table.
A hit skips the body. A miss runs the recursive body, stores its result,
and reads the actual stored winner.
Selection retains its exact pending, unresolved, identity, and exhausted outcomes.

`SourceCurrentMemoMergeWorkerProofs` proves both directions of completed
graph correspondence. Each finite graph supplies sufficient work and
selection bounds. Every larger pair returns the same result, heap, and table.
The common bound follows from the local selection receipts and actual mutual
graph induction. No recursive completion or global comparison-bound premise
is supplied. Work fuel bounds interpreter depth. It does not count all work.

`SourceCurrentMemoMergeWorkerComplete.source_cold` derives a finite call from
the initial physical invariants. The same call supplies stable executable
completion, independent language coverage, actual producer history, and
its ordered three-global-table effect. Only the completed merge table starts
empty. The physical heap and global tables can contain valid entries.

## Fields through the same class pass

`SourceCurrentMemoMergeFieldHeap` derives annotation safety for each actual
merge body. Mutual Run/Call induction retains the physical annotation heap.
Requests use their actual induction result. Hits do not replay their bodies.
The initial resident edge supplies each copied guard annotation.

`SourceCurrentMemoTargetFieldHeap` transfers these facts through projection,
target folds, stored target hits, and actual leaves.
`SourceCurrentMemoClassFieldHeap` transfers them through simultaneous edits,
rows, class right folds, and final empty propagation.
`pass_fields` specializes the annotation to normalized equality fields.
The proof needs selected closed paths. Unselected siblings can remain open.
It assumes no future field heap and no equality between old and new graphs.

## Physical entry composition

`SourceCurrentMemoPhysicalClassPass.live_scan_pass` starts with the actual
live physical entry and a successful Scan. It derives the retained records,
finite required execution, and selected path domains at the returned heap.
A reached range plan then derives a finite memo-aware class pass.

The same returned pass supplies final readiness, costs, normalized fields,
available original and result values, retained entries, completed merge
records, producer histories, fourth emptiness-memo correctness, and ordered
three-global-table receipts. The merge table passes between classes.
Each class starts only its own target slots empty.

Every output term belongs to the original input language and has the required
paths. Every original input term that satisfies the retained original classes
survives. Narrowing need not enforce the classes. The exact caller must still
check the original constraints.

## Boundaries

Successful Scan and actual-prefix range checks remain premises.
General Scan and outer constrained-call completion remain open.
The new executable theorem covers the merge interpreter. Executable target,
leaf, edit, and class workers still need connection to the new memo-aware
graphs. Earlier executable class proofs retain their older graph scopes.

Whole-pass pending publication, actual GHC demand, concurrency, identities,
host cache operations, HashMap outer iteration and allocation order, checked
native allocation transfer, and machine bounds remain separate obligations.
CostHeap is a stored invariant. It is not a wall-clock bound.

Continue the other full-library targets and every distinct Sized contract.
The aggregate audit, focused probes, and preservation evidence use
`/tmp/mcfta-memo-workers-*`.
