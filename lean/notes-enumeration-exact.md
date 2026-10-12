# Exact finite-term support of the actual enumeration driver

`EnumerationExact.runs_exact` proves the following equivalence for the actual
initialized `EnumerationState.runs` action:

- The root graph node accepts the finite term.
- Some finite execution bound produces that term, a residual list, and a final
  state. Every returned residual predicate holds on its returned subtree.

`runs_complete_eventually` gives one bound, residual list, and final state that
work at every larger bound. The proof constructs existence of a sufficient
bound. It does not state a closed-form numeric bound.

`EnumerationLanguage.accepted_iff` maps the complete graph to the existing
guarded `Language.Automaton`. `bounded_terms_exact` identifies the finite list
at each term height. `runs_uniform_height_bound` gives one sufficient driver
bound for every accepted term up to that height. The same equivalence holds
at every larger driver bound.

The theorem requires `CompleteGraph` and `IntersectionCorrect`. These are
graph-interface contracts. `CompleteGraph` excludes recursive marker views
and requires canonical edge tries with valid child indices.
`IntersectionCorrect` requires the exact accepted-language intersection law.
The constructor adapter below derives both contracts from source row
readback. Recursive
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

`EnumerationConstructors` models `mkEdge` contradiction and maximum-index
checks, the empty-child sentinel, and `mkNode` filtering. Every surviving row
has valid equality tries and valid child indices. Constructor-only node
readback therefore gives `CompleteGraph`. The readback relation permits
source identity deduplication and reordering. The module also proves that
`setChildren` preserves validity when the arity stays equal.

`EnumerationIntersection.joinedRows_member` proves that the actual
constructor-key hash join and equal-arity branch produce exactly the guarded
product rows. `HashRows.product` accounts for the closed self-intersection
shortcut and removal of false guards and empty children.
`intersection_correct` derives the language intersection law.
`EnumerationIntersection.runs_exact` uses these constructor and row contracts
in place of the two semantic graph premises.

`EnumerationEquality` derives canonical trie readback, equality conjunction,
and contradiction from the proved source equality normalizer.
`edgeView_conjoin` combines this equality result with residual conjunction.
`edgeView_contradiction` proves that a rejected equality conjunction has a
false product guard. The nontrivial-class premise holds for normalized source
classes; empty and singleton input classes must first pass normalization.

`EnumerationBoundedRows` implements the constructor part of `boundDepth`.
It copies ordered children, retains symbols and constraints, filters leaves
at the last level, and removes rows with empty bounded children. It derives
`CompleteGraph` from valid source edges. `accepted_exact` proves exact source
acceptance at the specified height, including empty-child removal.
`boundedMeet` intersects the source states at the smaller remaining height.
The source hash-row contract derives its intersection law.
`EnumerationBoundedRows.runs_exact` composes this construction with the actual
driver. It needs no assumed bounded-graph language or complete-node invariant.
Its identity table represents memo keys with a decoding left inverse. Actual
interning can merge equal rows; mapping those shared identities remains a
separate representation proof.

`EnumerationSharedRows` removes that injective-identity requirement. Its
row readback permits multiple memo keys to name the same runtime identity.
It derives bounded acceptance and exact driver support from those copied
rows. `EnumerationInternedRows` supplies the concrete `Cache.intern` step:
cache hits and misses return the requested immutable row key, valid keys
preserve `CompleteGraph`, and later cache growth preserves all already issued
child reads. `step_final_readback` proves the constructor's row equation at a
later cache snapshot. The premise covers only children read by that one
step. A full bounded-worker trace must compose these scoped steps; a finite
cache is not assumed to contain outputs for every possible depth bound.

This theorem identifies finite-term support. It does not remove duplicate
derivations or assign a probability to the source output list. Those counts,
ranks, and probabilities require their own source correspondence.

Binder-to-constructor row conversion, interned identity and cache readback,
residual-guard conjunction, mutable storage, Haskell laziness, and runtime
termination remain source-adapter obligations. The source `boundDepth`
worker unfolds `Mu` at the same depth and emits only constructor nodes or
empty nodes. Its `Rec` arm reports an error. The finite graph theorem starts
after this binder-to-row correspondence; it does not prove that runtime arm
unreachable from every public Haskell input.
The theorem applies to the executable Lean state machine once those
interfaces are established. It does not claim that the Haskell compiler or
runtime has been verified.

Validation: `lake -d lean build MicroCFTA.EnumerationInternedRows`. The modules use
the Lean kernel and existing `Std` definitions. They contain no omitted
proofs, axioms, or native evaluation proofs.
