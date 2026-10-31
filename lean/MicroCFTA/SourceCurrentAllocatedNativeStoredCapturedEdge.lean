import MicroCFTA.SourceCurrentAllocatedNativeStoredSelectedEdge
import MicroCFTA.SourcePruningEnumerationNativeBranchResources

/-!
# Native structural certificates at actual captured-edge observations

Current slot facts derive the selected-parent admission properties.
None and unhandled expose no caller and establish no native property.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredCapturedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

/-- Every exposed captured-edge caller retains native certificates under its current reservation. -/
theorem captured_edge_native_stored
    {bits : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h k uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed
      (SourcePruningEnumerationNativeBranchCompletion.edgeCost scs before.core.counter edge))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (nativeStored : Stored caller.checked.native) :
    match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k uv scs edge caller before memos.query with
    | none => True
    | some .unhandled => True
    | some (.rejected reached _ _) => Stored reached.checked.native
    | some (.stopped _ observation _) => Stored observation.2.1.checked.native
    | some (.complete _ reached _ _) => Stored reached.checked.native := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
      simp only [SourcePruningEnumerationCapturedEdge.run,
        SourcePruningEnumerationSelectedEdge.unsupported checkEmpty r n p h k scs edge caller before
          memos.query allowed projected]
    | some pair =>
      rcases pair with ⟨tries, residual⟩
      have actualCost : SourcePruningEnumerationNativeBranchCompletion.edgeCost scs before.core.counter edge =
          SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
        simp only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, allowed, ↓reduceIte, projected]
      have actualReserved : Reserved bits seed
          (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
        simpa only [actualCost] using reserved
      have edgeStored := SourceCurrentAllocatedNativeStoredSelectedEdge.selected_edge_native_stored seed
        formulas solver inventory caller before checkEmpty r n p h k parentEntry edges depth free edge scs
        roots memos initial available closed selected ready.safe realized paths counts flags bounded pending
        allowed tries residual projected fits actualReserved known nativeStored
      rw [SourcePruningEnumerationCapturedEdge.run]
      cases edgeObserved : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller
          before memos.query with
      | unhandled => trivial
      | rejected reached saved after =>
        simpa only [edgeObserved] using edgeStored
      | stopped processed observation candidate =>
        simpa only [edgeObserved] using edgeStored
      | complete fragment reached saved after =>
        dsimp only []
        cases finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k uv
            fragment after with
        | none => trivial
        | some finished =>
          simpa only [edgeObserved, Option.map_some] using edgeStored
  · have rejected : arityAllows edge.children.length scs = false := by
      cases actual : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed actual).elim
    simpa only [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge caller before
        memos.query rejected] using nativeStored

end MicroCFTA.SourceCurrentAllocatedNativeStoredCapturedEdge
