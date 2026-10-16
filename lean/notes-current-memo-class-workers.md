# Executable memo-aware targets, edits, and physical class passes

Source main is `6baa0e25`, merged at `416f0f39`.
This increment retains the optimized interned core and every earlier proof.
It adds executable correspondence for the current completed merge-table graphs.

## Targets and shared leaves

`SourceCurrentMemoTargetWorker` executes projection, memo-aware merging,
and native intersection. A target operand projects before it merges.
The target fold executes its current operand, its remaining fold, then
its native intersection. An empty target returns Empty without a demand.
Every outcome retains the actual native state and completed merge table.
Projection and native failures retain their complete observations.

`SourceCurrentMemoTargetWorkerProofs` derives actual Operand, Fold, and Target
traces from successful execution under the reached range checks.
Actual finite traces derive five sufficient bounds. Every larger tuple
returns the same value, native state, and merge table.
`SourceCurrentMemoTargetWorkerComplete.target_finite` constructs its trace
from initial physical invariants, selected path domains, and reached ranges.
It needs no supplied recursive completion or language-cache invariant.
Unselected original siblings can remain open.

`SourceCurrentMemoSharedLeafWorker` executes the class-local target slots.
A hit returns its exact stored value and the entire original shared state.
A miss executes the actual Target worker. Completion stores its result,
native state, and returned merge table. Failure retains the reached native
state and table without installing an incomplete target.
The following native leaf step retains that table and the earlier slots.
Its incomplete observation retains the native interpreter continuation.

The shared-leaf Proofs and Complete modules derive graph correspondence,
stable bounds, and finite execution from the physical selected-domain laws.
No incomplete observation becomes a successful value.

## Simultaneous edits and class folds

`SourceCurrentMemoSharedEditWorker` executes the current signed edit trie.
It applies an edit leaf before it inspects the node. A selected child runs
before the remaining child list. Edge construction precedes the next row.
Mu and union nodes execute their head read before recursive editing.
Constructor work changes only the heap in the full shared state.
Failures stop the enclosing control at the reached state.

Its Sound module derives the actual edit graphs from successful outputs.
Its Complete module derives six stable bounds from actual finite graphs.
The bounds cover edit depth, projection, head reads, merge instructions,
merge comparison, and native intersection. Componentwise maxima combine
siblings and adjacent operations. Bounds do not count total runtime work.

`SourceCurrentMemoClassWorker` executes the source right fold.
Each class captures the forest, native state, and merge table returned by
its actual tail. Only its class-local target slots start empty.
A failed class retains its captured forest and full shared observation.
Literal empty propagation runs once after the complete fold.

`SourceCurrentMemoClassWorkerProofs` derives successful graph correspondence
and stable completion for classes, folds, and passes. Six sufficient bounds
also give one sufficient common bound. Every larger common bound returns
the same result and both final states.

`SourceCurrentMemoClassWorkerComplete.finite` constructs one actual pass
from warm initial physical invariants, selected domains, and reached ranges.
It then derives a uniform executable bound for that same pass.
`source_cold` additionally derives independent language bounds, merge producer
histories, and the ordered three-global-table receipt. Only its completed
merge table starts empty. The native heap and global tables can be warm.

## Physical entry and semantic result

`SourceCurrentMemoPhysicalClassWorker.live_scan_pass` starts with the live
physical class entry and an actual successful Scan. It derives the retained
records, finite required-path execution, and selected domains at the returned
heap. Its reached range plan then constructs one finite executable class pass.

The same pass supplies StableRun, a sufficient common bound, readiness,
stored costs, normalized physical fields, available values, retained entries,
completed merge records, producer histories, fourth-memo correctness, and
ordered receipts for the three global tables.

Every output term belongs to the original input language and has the required
paths. Every original term that satisfies the retained original classes
survives. The narrowing result need not enforce those classes. The exact
caller must still check the original constraints.

## Boundaries

Successful Scan and actual-prefix native range checks remain premises.
The finite endpoints do not prove general Scan or outer constrained-call
completion. Failure retention does not prove arbitrary failed-state physical
invariants, automatic resumption, or an emptiness verdict.

These graphs describe completed sequential execution. The source IntMap
folds and shared closures are lazy. The proofs do not establish literal GHC
forcing or cache-allocation order. Early lazy publication, pending ancestors,
concurrent forcing, runtime identities, literal HashMap outer iteration,
checked constructor allocation, host containers, and machine bounds remain
separate obligations.

The older constructor and equality work remains a secondary target.
Continue every distinct Sized contract and all other full-library targets.
Evidence uses `/tmp/mcfta-memo-target-workers-*`.
