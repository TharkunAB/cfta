# Assignment semantics of concrete enumeration

`EnumerationSemantics.lean` composes the concrete state actions from
`EnumerationState.lean`. It imports the derived storage, scheduler, and
protected-root invariants in `EnumerationSchedule.lean` and
`EnumerationDriver.lean`.

## Checked semantic laws

`assimilate_assignment` and `mergeNode_assignment` extract the successful
source branches and apply the exact slot semantics. They cover duplicate
assimilation and structural-empty rejection.

`mergeTerminal_assignment` proves an equivalence for the complete actual
terminal merge. The final state denotes exactly the prior complete
assignments that equate every selected suspended variable. Its proof follows
the representative pre-scan, every union, the winning representative lookup,
and every assimilation. `mergeTerminal_backward` also identifies the term
assigned to the returned root with each original suspended variable.

`enumerateNode_terminal_assignment` proves an exact equivalence for the
entire terminal node branch. It adds the node-language restriction and all
inherited suspended equalities.

`enumeration_backward` follows the actual mutual `enumerateNode` and
`enumerateEdge` traversal. A satisfying final assignment implies a satisfying
prior assignment, acceptance of the returned completed fragment, and all
inherited suspended equalities. The proof includes fresh equality allocation,
ordered child traversal, edge-class reconstruction, and retained residuals.
The final-assignment premise is explicit. The theorem does not construct that
assignment or prove existence of an execution branch.

## Scope and next obligations

`CompleteGraph` excludes recursive marker views and requires canonical edge
tries whose paths fit the edge arity. `IntersectionCorrect` states the graph
primitive's exact language law. `ValidSuspended` requires canonical inherited
tries. Allocation bounds and root liveness use the derived `Safe` invariant.

The source explicitly drops descendant constraints below truncated recursive
binders. See the `terms` documentation in `Enumeration.hs`. Those markers have
a diagnostic contract. They are not finite accepted terms. The complete-term
theorem must connect its graph premise to the source bounded graph path.

`EnumerationFrame.enumeration_neutral` proves that replacing the selected
root payload with a neutral live slot leaves the actual child execution
unchanged. `enumerateOut_backward` uses that execution theorem to establish
the old pending restriction from the produced fragment. It does not assume
the root's pending language during its own expansion.

`EnumerationValidity` derives canonical stored tries through allocation,
intersection, all terminal operations, the mutual node and edge traversal,
and the final root write. `EnumerationSoundness.enumerateFully_backward`
composes these derived invariants through the complete actual caller.

`runs_assignment_sound` starts at the real initialized state and includes the
actual root and residual renderers. Under a satisfying final assignment, it
proves acceptance of the returned term and every returned residual predicate.
The final assignment remains an explicit premise. Its existence has not been
derived from the returned rendered term and residual checks.

No-loss still needs a constructive execution proof from each accepted term,
fresh-variable witness extension, sufficient execution bounds, and exclusion
of an unjustified stuck branch. A satisfying final assignment and successful
execution are premises of the current backward theorem. They are not proofs
of those remaining obligations.

Validation: `lake -d lean build MicroCFTA.EnumerationSoundness`.
