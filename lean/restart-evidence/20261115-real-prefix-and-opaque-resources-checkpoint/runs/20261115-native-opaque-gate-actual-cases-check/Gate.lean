import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueObservedResources
namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualOpaqueTerminalResources
set_option autoImplicit false
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem opaque_receipt_shape_gate
    (checkEmpty : Bool) (workFuel uv : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (empty : value ≠ .empty)
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false) :
    SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
      workFuel workFuel workFuel workFuel workFuel uv scs value caller before queries =
match ChildDispatch.run checkEmpty workFuel workFuel workFuel workFuel workFuel scs value caller before queries with
        | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel uv fragment after with
            | some finished => some (.complete fragment reached saved finished)
            | none => some (.finalizeStopped fragment reached saved after)
        | (observation, candidate) => some (.stopped [] observation candidate) := by
  unfold SourcePruningEnumerationSharedSelectedOpaqueDispatch.run
  rw [ite_eq_right empty]
  cases value <;> simp only [dispatch, Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' first | rfl | split
#print axioms opaque_receipt_shape_gate
end ActualOpaqueTerminalResources
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
