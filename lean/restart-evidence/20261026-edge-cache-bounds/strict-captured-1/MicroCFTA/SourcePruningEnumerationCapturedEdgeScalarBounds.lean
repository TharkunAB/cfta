import MicroCFTA.SourcePruningEnumerationSelectedEdgeScalarBounds
import MicroCFTA.SourcePruningEnumerationCapturedEdge

/-!
# Original scalar bounds after the captured-slot write

Selected-edge execution supplies the actual returned cache. Finalization
keeps its counter and cannot add suspended mass. Stops retain their own
optional cache. Unhandled results and absent caches remain explicit.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every attached captured-edge cache satisfies the original edge bounds, including rejection. -/
theorem observed_scalar_bounds
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    match run checkEmpty r n p h k target scs edge caller before queries with
    | none | some .unhandled => True
    | some (.complete _ _ _ after) | some (.rejected _ _ after) =>
        after.core.counter ≤ before.core.counter + tries.length + edge.children.length ∧
          suspendedBound after.core ≤ suspendedBound before.core +
            edge.children.length * (scs.length + tries.length)
    | some (.stopped _ _ candidate) =>
        ∀ after, candidate = some after →
          after.core.counter ≤ before.core.counter + tries.length + edge.children.length ∧
            suspendedBound after.core ≤ suspendedBound before.core +
              edge.children.length * (scs.length + tries.length) := by
  have selectedBounds := SourcePruningEnumerationSelectedEdge.observed_scalar_bounds
    checkEmpty r n p h k scs edge caller before queries tries residual projected
  unfold run
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | unhandled => trivial
  | rejected reached saved after =>
    simpa only [selected] using selectedBounds
  | stopped fragments observation candidate =>
    simpa only [selected] using selectedBounds
  | complete fragment reached saved middle =>
    simp only [selected] at selectedBounds
    cases finished : SourcePruningEnumerationFinalize.run
        reached.checked.native.machine.heap k target fragment middle with
    | none => trivial
    | some after =>
      dsimp only
      have finalBounds := SourcePruningEnumerationFinalize.run_scalars
        reached.checked.native.machine.heap k target fragment middle after finished
      exact ⟨by rw [finalBounds.1]; exact selectedBounds.1,
        Nat.le_trans finalBounds.2 selectedBounds.2⟩

end MicroCFTA.SourcePruningEnumerationCapturedEdge
