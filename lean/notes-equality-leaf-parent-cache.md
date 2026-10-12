# Source-first parent correspondence with finite preparation

`EqualityLeafProjectionParentCache` executes a finite cache preparation.
It runs the selected original child requests and then the original rebuilt
edge requests. `prepare_correct` derives coherence and cache growth.
`prepared_parent` proves parent normalization at any later coherent cache.
It derives child readback stability and edge residency from the executed
requests. It does not assume a globally complete cache or a parent law.

The preparation retains duplicate and dead original rows. Required-path
preparation runs child workers only for rows that pass the original arity
filter. The later edge preparation can allocate unused discarded-row keys.
Those proof-only requests do not change the source's retained row set.

`EqualityLeafProjectionParentStep.edit_parent` runs the actual source worker
first, on the stored canonical parent and the supplied current cache. The
proof then performs finite preparation. It derives that the already returned
source value equals parent reconstruction from all original occurrences
using final actual child readbacks. The theorem includes an original parent
that normalizes to EmptyNode. The edit list is nonempty and has no root edit.

`require_parent` proves the corresponding source-first result for proper
child requirements. Reconstruction includes only original rows that pass
the original arity check. The source worker's child evaluation order and
arity rejection remain unchanged. Unselected edits and root-only requirements
use the existing direct-return equations.

The actual parent worker executes before proof preparation. Thus these
results do not replace source allocation order with a preparation-first
implementation. The common later cache lets the proof compare complete
physical records even when original provenance contains extra erased rows.
The remaining step connects each original child occurrence recursively to
its edited occurrence representation, and composes those finite results
through the fixed equality schedule and its root-empty propagation.
