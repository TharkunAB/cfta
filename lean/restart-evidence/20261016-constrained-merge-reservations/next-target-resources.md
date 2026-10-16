# Next proof: Target cumulative resources

Start with the actual graph in `SourceCurrentAllocatedTargetGraph.lean`
and the checked receipts in `SourceCurrentAllocatedTargetComplete.lean`.
Read the structural fold induction in
`SourceCurrentAllocatedFiniteOrdinaryTarget.lean`.
The head Operand executes before the recursive tail. The native query
executes after that tail at its returned checked state. Keep this order.

Use OperandResources.complete to construct each operand receipt from
initial forest, path, row, arity, length, and height bounds. Retain its actual
heap, saved Merge table, generated output profile, and constructor trace.
Carry that profile and original forest availability through the actual tail.
Use the native output profile and static budget results for the next query.
Compose all traces at the literal intermediate heaps. Derive later input
profiles and capacity from earlier returns and initial total headroom.

Do not take a completed Target, a future query profile, a future count, or
capacity at every reached query as the public initial premise. Those facts
must follow from the initial bounds. Legitimate initial warm-table laws,
semantic readiness, solver contracts, and available inputs stay explicit.
Cold endpoints must derive empty-table laws.

Then compose shared edits, class passes, local calls, parent calls, and
the outer pass. The endpoint to discharge is
SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan. It requires
numeric parent capacity at each independently reached entry. The existing
OuterNumericRoot endpoint constructs stable literal execution and preserves
the full guarded language when that plan holds. Initial source-build
capacity alone does not prove the plan.

Constructor resources do not cover equality, domain, sidecar, thunk,
instruction, host forcing, signed-counter, or concurrent-candidate resources.
Keep those boundaries explicit. General Mu/reference/union progress,
repeated-pass convergence, frontend correspondence, concrete Haskell,
and full-library composition remain separate obligations.
