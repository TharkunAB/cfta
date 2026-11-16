# Current model and one clear

The existing `selected_parked_arrow_bucket_assignment` in SharedProperPathWitness
assigns var1 to every non-owner class. SharedArrowBucketFragmentWitness extends
that choice through fragments at the OLD stored-bucket snapshot. This is a
separate witness from the current assignment and rendering result.

The new local constructor starts with one supplied final term assignment.
It chooses each used arrow child from that assignment. It changes only the
owner class. It retains all raw target values and UF equations. The only var1
fallback occurs at a child position with no represented constraint.

Pointwise agreement outside the owner class does not by itself retain stored
fragment equations. A fragment may evaluate a dependency through another
expanded slot. `stratified_extend_pending` reconstructs stored equations but
promises agreement only at directly pending slots. The historical raw targets
need not remain pending. `stored_bucket_holds_transfer` requires a currently
stored bucket and PendingReferences, so it cannot silently transfer a removed
historical bucket at the final state.

The original906 theorem supplies direct fragment avoidance and held-class
protection. Evaluator noninterference, actual source raw-target agreement,
current domain preservation, residual checks, guards, and ALL earlier removed
obligations still need a joint proof. This packet does not combine independent
witnesses or establish a full accepted completion of the original root.
