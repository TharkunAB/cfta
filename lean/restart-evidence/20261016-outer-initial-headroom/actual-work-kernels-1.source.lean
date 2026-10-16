import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualClassPassWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts

namespace MicroCFTA.ActualWorkChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open MergedOrdinaryHeight (height childrenHeight)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "OutRows" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputRows
local notation "OutArity" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputArity
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PassRows" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputRows
local notation "PassArity" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputArity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}

/-- Two actual Empty callbacks retain one captured slot envelope without any constructor headroom premise. -/
theorem repeated_empty_positions
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before middle after : Shared width} {firstValue secondValue : Value Symbol Guard}
    {inventory firstInventory secondInventory : Inventory} {memos current final : Memos}
    (first : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver firstInventory record originals base path
      .empty before firstValue middle memos current)
    (second : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver secondInventory record originals base path
      .empty middle secondValue after current final)
    (ready : Ready formulas solver inventory record originals base before)
    (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (captured : ChildrenShape rows arity originals)
    (lengthBound : originals.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (capturedHeight : childrenHeight originals ≤ bound)
    (stored : Stored (TargetRows record rows count depth bound) (max arity 1) bound before)
    (valid : Valid before.checked.native.machine.heap memos) :
    ∃ actual : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 0
        ([.empty, .empty] : List (Value Symbol Guard)) before [firstValue, secondValue] after,
      ChildrenReads formulas solver base actual memos final ∧ ChildrenCount actual 2 ∧
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      ChildrenShape (OutRows record rows count depth bound 0) (OutArity arity 0) [firstValue, secondValue] ∧
      childrenHeight [firstValue, secondValue] ≤ 0 ∧
      ∃ next, SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record originals base
        ([.empty, .empty] : List (Value Symbol Guard)) before [firstValue, secondValue] after memos final ∧
        ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
          nodeRequests requests ≤ 2 * SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafNodes record rows arity count depth bound 0 0 0 ∧
          edgeRequests requests ≤ 2 * SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafEdges record rows arity count depth bound 0 0 0 := by
  let firstNode := EditNode.leaf first.actual
  let secondNode := EditNode.leaf second.actual
  let tail : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 1
      ([.empty] : List (Value Symbol Guard)) middle [secondValue] after := .selected 1 rfl secondNode .nil
  let actual : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 0
      ([.empty, .empty] : List (Value Symbol Guard)) before [firstValue, secondValue] after := .selected 0 rfl firstNode tail
  have reads : ChildrenReads formulas solver base actual memos final :=
    .selected (found := rfl) (first := firstNode) (rest := tail) (.leaf first)
      (.selected (found := rfl) (first := secondNode) (.leaf second) .nil)
  have populated : Populated (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Populated]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by simp only [Populated], [], path, by simp [leaves]⟩
  have allowed : Allowed record (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Allowed, All]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa only [All] using member
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
  have produced := SourceCurrentAllocatedFiniteOrdinaryActualEditWork.children reads populated allowed ready available safe valid
    known coherent rows arity count depth bound 0 0 0 captured lengthBound pathsBound capturedHeight stored
    (show ChildrenShape 0 0 ([.empty, .empty] : List (Value Symbol Guard)) from ⟨trivial, trivial, trivial⟩) (by decide)
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects reads populated allowed ready available safe valid
  refine ⟨actual, reads, .selected (found := rfl) (.leaf first.actual) (.selected (found := rfl) (.leaf second.actual) .nil),
    produced.1, produced.2.1, produced.2.2.2.2.1, next, receipt, ?_⟩
  obtain ⟨requests, work, nodes, edges⟩ := produced.2.2.2.2.2
  refine ⟨requests, work, ?_, ?_⟩
  · simpa [SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenNodes,
      SourceCurrentAllocatedFiniteOrdinaryValuePositions.children, SourceCurrentAllocatedFiniteOrdinaryValuePositions.node,
      SourceCurrentAllocatedFiniteOrdinaryOccurrences.children, SourceCurrentAllocatedFiniteOrdinaryOccurrences.node] using nodes
  · simpa [SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenEdges,
      SourceCurrentAllocatedFiniteOrdinaryValuePositions.children, SourceCurrentAllocatedFiniteOrdinaryValuePositions.node,
      SourceCurrentAllocatedFiniteOrdinaryOccurrences.children, SourceCurrentAllocatedFiniteOrdinaryOccurrences.node] using edges

/-- A second actual query consumes the first actual result profile without any constructor capacity premise. -/
theorem serial_native
    {left right first result : Value Symbol Guard} {before middle after : SourceEqualityNativeDemand.State width}
    {inventory : Inventory} {memos : Memos}
    (receipt : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before first middle memos)
    (second : SourceCurrentAllocatedTargetQuery.Step first left middle result after)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (output : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored before.native)
    (rows arity bound : Nat) (leftProfile : NodeShape rows arity left) (rightProfile : NodeShape rows arity right)
    (heightBound : max (height left) (height right) ≤ bound) :
    SourceCurrentAllocatedFiniteOrdinaryStored.Stored after.native ∧
      SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored after.native ∧
      NodeShape ((rows * rows) * (rows * rows)) (max arity 1) result ∧ height result ≤ bound ∧
      ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests + edgeRequests requests ≤
          SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget rows arity bound +
          SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget (rows * rows) (max arity 1) bound := by
  obtain ⟨middleNative, middleOutput, firstProfile, firstHeight, _rightHeight, firstRequests, firstTrace, firstCount,
    _firstNodes, _firstEdges⟩ := SourceCurrentAllocatedFiniteOrdinaryActualNativeWork.counted rows arity bound receipt.actual
      ready native output leftProfile rightProfile heightBound
  have leftHeight : height left ≤ bound := Nat.le_trans (Nat.le_max_left _ _) heightBound
  obtain ⟨lastNative, lastOutput, resultProfile, resultHeight, _leftHeight, lastRequests, lastTrace, lastCount,
    _lastNodes, _lastEdges⟩ := SourceCurrentAllocatedFiniteOrdinaryActualNativeWork.counted (rows * rows) (max arity 1) bound
      second receipt.ready middleNative middleOutput firstProfile
      (NodeShape.mono left leftProfile (Nat.le_mul_self rows) (Nat.le_max_left _ _))
      (Nat.max_le.mpr ⟨Nat.le_trans firstHeight leftHeight, leftHeight⟩)
  refine ⟨lastNative, lastOutput, by simpa only [Nat.max_assoc, Nat.max_self] using resultProfile,
    Nat.le_trans resultHeight (Nat.le_trans firstHeight leftHeight), firstRequests ++ lastRequests, firstTrace.trans lastTrace, ?_⟩
  rw [nodeRequests_append, edgeRequests_append]
  omega

end MicroCFTA.ActualWorkChecks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.ActualWorkChecks.repeated_empty_positions
#check @MicroCFTA.ActualWorkChecks.repeated_empty_positions
#print axioms MicroCFTA.ActualWorkChecks.serial_native
#check @MicroCFTA.ActualWorkChecks.serial_native
