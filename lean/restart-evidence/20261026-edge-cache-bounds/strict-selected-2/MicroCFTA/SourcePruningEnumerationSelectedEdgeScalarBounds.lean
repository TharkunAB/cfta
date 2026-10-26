import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourcePruningEnumerationTraversalScalarBounds
import MicroCFTA.SourcePruningEnumerationBucketSumBounds

/-!
# Original scalar bounds at actual selected-edge returns

The actual own prefix supplies the original child buckets. Their complete
sum bounds the reached traversal cache. Residual recording preserves both
scalars. Stopped results retain only their actual optional cache.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
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

/-- Every actual selected-edge cache satisfies bounds from its original counter and buckets. -/
theorem observed_scalar_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    match run checkEmpty r n p h k scs edge caller before queries with
    | .unhandled => True
    | .complete _ _ _ after | .rejected _ _ after =>
        after.core.counter ≤ before.core.counter + tries.length + edge.children.length ∧
          suspendedBound after.core ≤ suspendedBound before.core +
            edge.children.length * (scs.length + tries.length)
    | .stopped _ _ candidate =>
        ∀ after, candidate = some after →
          after.core.counter ≤ before.core.counter + tries.length + edge.children.length ∧
            suspendedBound after.core ≤ suspendedBound before.core +
              edge.children.length * (scs.length + tries.length) := by
  unfold run
  cases prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before with
  | none => trivial
  | some rows =>
    cases rows with
    | nil =>
      exact ⟨by omega, Nat.le_add_right _ _⟩
    | cons row rest =>
      rcases row with ⟨⟨symbol, staged, savedResidual⟩, middle⟩
      cases rest with
      | cons second remaining => trivial
      | nil =>
        have ownScalars := SourcePruningEnumerationCachedOwn.prepare_scalars
          caller.checked.native.machine.heap scs edge before middle tries residual
          (symbol, staged, savedResidual) projected prepared
        have ownInputs := SourcePruningEnumerationCachedOwn.prepare_inputs
          caller.checked.native.machine.heap scs edge before middle tries residual
          (symbol, staged, savedResidual) projected prepared
        simp only [Prod.mk.injEq] at ownInputs
        obtain ⟨rfl, rfl, rfl⟩ := ownInputs
        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
        have readback : ((inputs.map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
              (EnumGuard := Constraint) input.2 input.1))).map
            (fun input => (input.1, input.2.1))) = inputs := by
          simp only [List.map_map]
          exact List.map_id _
        have count : inputs.length = edge.children.length := by
          simp only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx]
        have bucketSum := SourcePruningEnumerationCostBounds.children_bucket_sum_le
          edge scs before.core.counter tries
        have traversalBounds := SourcePruningEnumerationChildTraversal.observed_scalar_bounds
          checkEmpty r n p h k inputs caller middle queries
        cases traversed : SourcePruningEnumerationChildTraversal.run
            checkEmpty r n p h k inputs caller middle queries with
        | complete fragments afterCaller saved after =>
          simp only [traversed] at traversalBounds
          change after.core.counter ≤ before.core.counter + tries.length + edge.children.length ∧
            suspendedBound after.core ≤ suspendedBound before.core +
              edge.children.length * (scs.length + tries.length)
          rw [count, ownScalars.2.2.1, ownScalars.2.2.2] at traversalBounds
          exact ⟨by omega, Nat.le_trans traversalBounds.2 (Nat.add_le_add_left bucketSum _)⟩
        | stopped fragments observation candidate =>
          simp only [traversed] at traversalBounds
          intro after recovered
          have bounds := traversalBounds after recovered
          rw [count, ownScalars.2.2.1, ownScalars.2.2.2] at bounds
          exact ⟨by omega, Nat.le_trans bounds.2 (Nat.add_le_add_left bucketSum _)⟩

end MicroCFTA.SourcePruningEnumerationSelectedEdge
