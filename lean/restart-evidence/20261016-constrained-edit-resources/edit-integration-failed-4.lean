import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts

set_option linter.all true
set_option pp.universes true

namespace MicroCFTA.EditResourceIntegrationChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Two selected source positions each execute one actual leaf callback. -/
theorem two_selected_count {record originals path first second before results after}
    (actual : EditChildren (width := width) record originals [(0, .editAt path), (1, .editAt path)] 0 [first, second] before results after) :
    ChildrenCount actual 2 := by
  cases actual with
  | unselected _ absent _ => simp [SourceEqualityNeededMap.lookup] at absent
  | selected _ found first rest =>
      simp [SourceEqualityNeededMap.lookup] at found
      cases found
      cases first with
      | leaf one =>
          cases rest with
          | unselected _ absent _ => simp [SourceEqualityNeededMap.lookup] at absent
          | selected _ found second rest =>
              simp [SourceEqualityNeededMap.lookup] at found
              cases found
              cases second with
              | leaf two =>
                  cases rest with
                  | nil => exact .selected (found := rfl) (.leaf one) (.selected (found := rfl) (.leaf two) .nil)

section Initial
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (bits : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared (bits + 2))
variable (rows arity count depth bound inputRows inputArity inputBound : Nat)
variable (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record)
variable (active : EqualityNormalize.Nontrivial record.paths) (captured : ChildrenShape rows arity originals)
variable (lengthBound : originals.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
variable (capturedHeight : childrenHeight originals ≤ bound) (inventory : Inventory)
variable (ready : Ready formulas solver inventory record originals base before)
local notation "TargetR" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafNodes record rows arity count depth bound inputRows inputArity inputBound
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafEdges record rows arity count depth bound inputRows inputArity inputBound
local notation "NN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes LeafN
local notation "NE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges LeafE
local notation "CN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenNodes LeafN
local notation "CE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenEdges LeafE
variable (stored : Stored (SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound) (max arity 1) bound before)
variable (path : EqualityNormalize.Path) (member : path ∈ record.paths)
variable (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
include known coherent active captured lengthBound pathsBound capturedHeight ready stored member valid

/-- Empty still invokes a node callback in the constructed resource execution. -/
theorem constructed_empty_leaf
    (nodes : before.checked.native.machine.heap.nodes.next + LeafN ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + LeafE ≤ 2 ^ (bits + 2)) :
    ∃ result after next final requests, ∃ actual : EditNode record originals (.editAt path) .empty before result after,
      NodeReads formulas solver base actual memos final ∧ NodeCount actual 1 ∧
      SourceCurrentAllocatedSharedEditEffects.NodeReceipt formulas solver next record originals base .empty before result after memos final ∧
      Stored TargetR (max arity 1) bound after ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ LeafN ∧ edgeRequests requests ≤ LeafE := by
  have safe : Safe (.editAt path) (.empty : Value Symbol Guard) :=
    closed_safe _ _ _ ready.checked.semantic (empty_available _) rfl
  have nodeCost : NN (.empty : Value Symbol Guard) = LeafN ∧ NE (.empty : Value Symbol Guard) = LeafE :=
    SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.node_empty LeafN LeafE
  obtain ⟨result, after, next, final, requests, actual, reads, receipt, retained, _produced, _narrow, _height,
    _stable, trace, nodeCount, edgeCount, _capacity, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryEditResources.node formulas solver bits record originals base rows arity count depth bound
      inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
      inventory (.editAt path) .empty before ready stored (empty_available _) trivial (Nat.zero_le _)
      (by simp only [Populated]) (by exact ⟨[], path, by simp [leaves]⟩) (by simpa only [Allowed, All] using member) safe memos valid
      (by simpa only [nodeCost.1] using nodes) (by simpa only [nodeCost.2] using edges)
  have counted : NodeCount actual 1 := by cases actual with | leaf leaf => exact .leaf leaf
  exact ⟨result, after, next, final, requests, actual, reads, counted, receipt, retained, trace,
    by simpa only [nodeCost.1] using nodeCount, by simpa only [nodeCost.2] using edgeCount⟩

/-- The concrete producer edits two repeated Empty positions, retaining the exact two-callback certificate. -/
theorem constructed_two_empty_leaves
    (nodes : before.checked.native.machine.heap.nodes.next + CN ([.empty, .empty] : List (Value Symbol Guard)) ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + CE ([.empty, .empty] : List (Value Symbol Guard)) ≤ 2 ^ (bits + 2)) :
    ∃ results after next final requests,
      ∃ actual : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) before results after,
        ChildrenReads formulas solver base actual memos final ∧ ChildrenCount actual 2 ∧
        SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record originals base ([.empty, .empty] : List (Value Symbol Guard)) before results after memos final ∧
        Stored TargetR (max arity 1) bound after ∧ results.length = 2 ∧
        SourceCurrentAllocatedSharedEditWorkerCompletion.StableRun
          (fun e p h m s n => SourceCurrentAllocatedSharedEditWorker.children
            (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n)
            [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) before) results after ∧
        Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ CN ([.empty, .empty] : List (Value Symbol Guard)) ∧ edgeRequests requests ≤ CE ([.empty, .empty] : List (Value Symbol Guard)) := by
  have populated : Populated (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Populated]
    intro index child included
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at included
    rcases included with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨by simp only [Populated], [], path, by simp [leaves]⟩
  have allowed : Allowed record (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Allowed, All]
    intro index child included
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq] at included
    rcases included with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simpa only [All] using member
  have available : Values before.checked.native.machine.heap ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro value selected
    have same : value = .empty := by simpa using selected
    exact same ▸ empty_available _
  have safe : ChildrenSafe [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro query child found value selected
    have same : value = .empty := by
      have present := List.mem_of_getElem? selected
      simpa using present
    subst value
    exact closed_safe _ _ _ ready.checked.semantic (empty_available _) rfl
  obtain ⟨results, after, next, final, requests, actual, reads, receipt, retained, _produced, _narrow, sameLength,
    stable, trace, nodeCount, edgeCount, _capacity, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryEditResources.children formulas solver bits record originals base rows arity count depth bound
      inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
      inventory [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) before ready stored available
      ⟨trivial, trivial, trivial⟩ (Nat.zero_le _) populated allowed safe memos valid nodes edges
  exact ⟨results, after, next, final, requests, actual, reads, two_selected_count actual, receipt, retained,
    sameLength, stable, trace, nodeCount, edgeCount⟩
end Initial

#print axioms two_selected_count
#check @two_selected_count
#print axioms constructed_empty_leaf
#check @constructed_empty_leaf
#print axioms constructed_two_empty_leaves
#check @constructed_two_empty_leaves
end MicroCFTA.EditResourceIntegrationChecks
