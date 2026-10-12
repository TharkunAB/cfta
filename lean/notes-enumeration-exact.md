# Exact finite-term support of the actual enumeration driver

`EnumerationExact.runs_exact` proves the following equivalence for the actual
initialized `EnumerationState.runs` action:

- The root graph node accepts the finite term.
- Some finite execution bound produces that term, a residual list, and a final
  state. Every returned residual predicate holds on its returned subtree.

`runs_complete_eventually` gives one bound, residual list, and final state that
work at every larger bound. The proof constructs existence of a sufficient
bound. It does not state a closed-form numeric bound.

The theorem requires `CompleteGraph` and `IntersectionCorrect`. These are
graph-interface contracts. `CompleteGraph` excludes recursive marker views
and requires canonical edge tries with valid child indices.
`IntersectionCorrect` requires the exact accepted-language intersection law.
The concrete source graph adapter must establish both contracts. Recursive
truncation markers retain their diagnostic contract and are not finite terms
accepted by this theorem.

## Derived execution facts

The proof has no internal assignment, state-invariant, transition-preservation,
successful-execution, or termination premise in its completeness direction.
It derives all such facts from initialization and acceptance.

`EnumerationTermination.initialized_complete` constructs the scheduler and
all selected expansions. Each expansion decreases the finite histogram of
pending term heights. Lower-height counts can increase without a fixed bound.

`EnumerationCarriers` proves that union, intersection, and duplicate
assimilation preserve each class's stored graph restriction or completed
fragment. `EnumerationGraphReferences` proves this provenance for every
returned hole, stored fragment hole, and retained residual hole.
`EnumerationRenderability.initialized_carriers` derives it for the complete
actual caller and root zero. `completed_carrier` excludes pure equality slots
from all those reachable references after completion.

`EnumerationRendering` combines this provenance with the derived strict
fragment dependency levels. It constructs root, fragment, and residual
rendering at sufficient finite bounds. `EnumerationExecution.runs_moreFuel`
combines the separate bounds without changing the successful returned state.

The soundness direction is `EnumerationAssignment.runs_sound`. It constructs
a complete solution of the final forest and fragment equations. The returned
residual checks establish the assignment's guard restrictions. Backward
execution semantics then proves initial acceptance.

## Remaining source boundary

This theorem identifies finite-term support. It does not remove duplicate
derivations or assign a probability to the source output list. Those counts,
ranks, and probabilities require their own source correspondence.

Concrete bounded graph construction, graph intersection, mutable storage,
Haskell laziness, and runtime termination remain source-adapter obligations.
The theorem applies to the executable Lean state machine once those
interfaces are established. It does not claim that the Haskell compiler or
runtime has been verified.

Validation: `lake -d lean build MicroCFTA.EnumerationExact`. The modules use
the Lean kernel and existing `Std` definitions. They contain no omitted
proofs, axioms, or native evaluation proofs.
