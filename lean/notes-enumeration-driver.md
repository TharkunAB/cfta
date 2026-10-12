# Concrete enumeration scheduler and caller

`EnumerationSchedule.lean` and `EnumerationDriver.lean` prove state invariants
for the actual actions in `EnumerationState.lean`. These actions follow
`microcfta/src/Data/CFTA/Enumeration.hs`. The proofs do not use a separate
transition relation with assumed preservation laws.

## Checked scheduler and caller laws

- `findExpandable_exact` follows both scheduler folds. It identifies the
  candidates and the representatives blocked by suspended constraints.
  `findExpandable_safe` proves that each offered index is a live root with no
  incoming suspended references.
- `mergeTerminal_valid` follows the representative scan, union loop, and
  assimilation loop. It restores `LiveRoots` after all selected roots merge.
  `mergeTerminal_storage` preserves allocation bounds.
- `enumeration_safety` proves that the actual mutual `enumerateNode` and
  `enumerateEdge` traversal preserves `StorageValid` and `LiveRoots`.
  It also bounds every hole in the returned fragment.
- `enumeration_protected` proves that child traversal preserves a selected
  root, its stored value, and its complete alias class. The proof composes
  fresh allocation, terminal unions, assimilation, node restriction, ordered
  child traversal, and residual recording.
- `enumerateOut_safe` derives the safety of the final root write. Its
  selected-root premise is established by `findExpandable_ready`.
- `enumerateFully_outcome` follows the complete caller. It proves safe
  storage, monotone allocation, and no remaining eligible slot. The proof
  includes repeated-recursion detection and constraint clearing.
  `finished_pending` proves that every remaining pending graph slot is an
  unconstrained recursive node.
- `runs_safe` starts at `initial`, executes the ordinary caller, renders the
  root, and renders every residual obligation. Every successful result has
  safe storage, at least one allocated slot, and no remaining eligible slot.
  Rendering preserves all stored values and obligations.

`ReadOnlyOracle` states an explicit callback interface: successful callback
execution leaves the enumeration state unchanged. `noPruning_readOnly`
proves this interface for the ordinary enumerator. The general caller theorem
uses this interface. A callback that performs representative lookup changes
the stored forest by compression. Such a callback requires a more permissive
verified interface before this general theorem applies to it.

## Remaining semantic obligations

The successful-state safety theorem does not prove that execution avoids all
internal errors. It does not prove that every finite accepted term has a
successful branch. It does not prove that returned terms satisfy the original
node language or residual predicates.

`EnumerationSoundness.runs_assignment_sound` now composes backward assignment
semantics through the full traversal and its final root write. See
`notes-enumeration-semantics.md`. That theorem assumes a satisfying final
assignment. `EnumerationAssignment.runs_sound` now constructs that assignment
from derived pending-reference and strict fragment dependency invariants.
It proves acceptance when the returned residual predicates hold. See
`notes-enumeration-assignment.md`. The proper-constraint invariant also
excludes the blocked scheduler result under a satisfying assignment.
`EnumerationExact.runs_exact` now proves existence at sufficient bounds and
exact finite-term support. See `notes-enumeration-exact.md`.

Recursive markers require the documented truncation contract. A marker is
not an accepted finite term. New edge equality classes require the source
constructor's validity and arity invariants. Graph intersection, recursive
exposure, mutable representations, and callbacks require source
correspondence at their actual interfaces.

Validation: `lake -d lean build MicroCFTA.EnumerationDriver`. The proofs use
the Lean kernel, `Std`, and existing project modules. They contain no omitted
proofs, axioms, or native evaluation proofs.
