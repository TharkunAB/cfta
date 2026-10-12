# Complete-run soundness and constructed assignments

`EnumerationAssignment.runs_sound` proves that a successful initialized
`runs` execution returns an accepted finite term when its returned residual
predicates hold. It derives all storage, reference, dependency, and assignment
facts from that execution.

The theorem requires `CompleteGraph` and `IntersectionCorrect` at the graph
interface. `CompleteGraph` excludes recursive marker views and requires valid
edge tries whose paths fit the edge arity. `IntersectionCorrect` states the
exact language law for graph intersection. The concrete bounded graph adapter
must establish those interfaces. Recursive markers retain their separate
diagnostic contract.

## Derived dependency invariants

`EnumerationDependencies` proves that child traversal preserves each old
enumerated payload. Returned holes avoid the selected root class.
`returned_hole_pending` proves that each returned hole has a pending root.

`EnumerationReferences` follows references from old state, inherited
constraints, and fresh equality variables. It proves that no suspended
constraint targets an enumerated root. `initialized_pending` derives this
fact through the scheduler and the final root write.

`EnumerationOrder.Stratified` assigns levels to equality classes. Each
enumerated slot has a smaller level than every hole in its fragment. Every
pending slot has the current frontier level. The actual final root write
advances the frontier. `initialized_stratified` derives this finite ordering
from the actual initialized caller.

## Constructed assignments and rendering

`evaluateSlots_stable` proves that evaluation stabilizes above the remaining
dependency levels. `stratified_assignment` solves every forest and stored
fragment equation. Free equality variables receive a fixed finite term.
`completed_assignment` derives that solution for every successful initialized
complete caller. It does not assume guard truth.

The root and residual renderers produce exactly the terms of this assignment.
The checked returned residuals therefore establish the stored guard
restrictions. Backward execution semantics then establishes initial root
acceptance. `runs_sound` has no assumed final assignment or internal
transition-preservation premise.

## Remaining obligations

`EnumerationConstruction.enumerateNode_complete` now constructs local
executions, fresh witness extensions, and successful required intersections.
`EnumerationTermination.initialized_complete` also constructs whole-caller
execution at a sufficient bound. See `notes-enumeration-construction.md`.
Sufficient bounds for the final renderers remain open. The successful-run
theorem does not establish renderer existence. Concrete source
graph and mutable representation correspondence remain separate obligations.

Validation: `lake -d lean build MicroCFTA.EnumerationAssignment`.
