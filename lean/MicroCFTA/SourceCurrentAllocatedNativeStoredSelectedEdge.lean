import MicroCFTA.SourceCurrentAllocatedNativeStoredChildTraversal
import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources

/-!
# Native structural certificates at actual selected-edge observations

The actual own-class prefix derives the child traversal admission facts.
Unhandled results expose no caller and establish no native property.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredSelectedEdge
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

/-- Every exposed selected-edge caller retains native certificates under its current reservation. -/
theorem selected_edge_native_stored
    {bits : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h k : Nat)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (nativeStored : Stored caller.checked.native) :
    match SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before memos.query with
    | .unhandled => True
    | .rejected reached _ _ => Stored reached.checked.native
    | .stopped _ observation _ => Stored observation.2.1.checked.native
    | .complete _ reached _ _ => Stored reached.checked.native := by
  obtain ⟨action, own, _prepared, ownRun, _raw, _ownCore, _ownCounter, _ownForest,
    ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending,
    genuine, _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
        input.2 input.1))).map (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  have traversalStored := SourceCurrentAllocatedNativeStoredChildTraversal.child_traversal_native_stored
    seed formulas solver inventory caller own checkEmpty r n p h k inputs roots memos initial ownSafe
    ownPaths ownCounts ownFlags ownRealized genuine fits reserved known nativeStored
  simp only [SourcePruningEnumerationSelectedEdge.run, ownRun]
  rw [readback]
  cases childrenObserved : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k inputs
      caller own memos.query with
  | complete fragments afterCaller saved after =>
      simpa only [childrenObserved] using traversalStored
  | stopped _processed observation candidate =>
      simpa only [childrenObserved] using traversalStored

end MicroCFTA.SourceCurrentAllocatedNativeStoredSelectedEdge
