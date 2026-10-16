import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualTargetWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedLeafResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedForceResources

/-!
# Actual constructor Work through shared force and leaf receipts

A hit uses no Work. A miss counts its same actual target before storing it.
Each leaf adds its same physical native query after the force return.
The fixed captured profile certifies warm slots throughout the edit.
No constructor headroom or future capacity is a premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualSharedWork
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open MergedOrdinaryHeight (height childrenHeight)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "ForceN" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget
local notation "ForceE" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget
local notation "targetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {input value result : Value Symbol Guard} {memos final : Memos}

/-- The same actual force derives its fixed target envelope and retains all certificate tables. -/
theorem force_receipt
    {receiptBase : InternedConstructorTemplates.State Symbol Guard}
    (receipt : ForceReceipt formulas solver next record values receiptBase path before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (targetRows record rows count depth bound) (max arity 1) value ∧ height value ≤ bound ∧
      ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ ForceN record rows arity count depth bound before path ∧
        edgeRequests requests ≤ ForceE record rows arity count depth bound before path := by
  cases receipt.reads with
  | hit present =>
      have zeroNodes : ForceN record rows arity count depth bound before path = 0 := by simp [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget, present]
      have zeroEdges : ForceE record rows arity count depth bound before path = 0 := by simp [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget, present]
      exact ⟨stored, (stored.slots path value present).1, (stored.slots path value present).2,
        [], .refl _, by simp [nodeRequests, zeroNodes], by simp [edgeRequests, zeroEdges]⟩
  | miss absent reads =>
      have available : Values before.checked.native.machine.heap values :=
        fun value member => ready.captured.available value (known value member)
      obtain ⟨merged, native, output, shaped, bounded, requests, work, nodes, edges, _nodeSupply, _edgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryActualTargetWork.target_reads reads ready.checked available ready.stored
          stored.merge stored.native stored.output rows arity count depth bound profile lengthBound
          (SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.operand_paths_depth record.paths path depth pathsBound) heightBound
      have operandCount := SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.record_operand_paths_length record coherent path member
      have produced : NodeShape (targetRows record rows count depth bound) (max arity 1) value := by
        simpa only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows, operandCount] using shaped
      exact ⟨SourceCurrentAllocatedFiniteOrdinarySharedProfiles.store_stored before path value _ _ stored
        native output merged produced bounded, produced, bounded, requests, work,
        by simpa only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget, absent, operandCount] using nodes,
        by simpa only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget, absent, operandCount] using edges⟩

/-- The same supplied leaf counts its actual force and native query in order. -/
theorem leaf_receipt
    (receipt : LeafReceipt formulas solver next record values base path input before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound)
    (inputRows inputArity inputBound : Nat) (inputProfile : NodeShape inputRows inputArity input)
    (inputHeight : height input ≤ inputBound) :
    Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (max (targetRows record rows count depth bound) inputRows *
        max (targetRows record rows count depth bound) inputRows) (max (max (max arity 1) inputArity) 1) result ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result ∧ height result ≤ inputBound ∧
      ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ LeafN record rows arity count depth bound inputRows inputArity inputBound before path ∧
        edgeRequests requests ≤ LeafE record rows arity count depth bound inputRows inputArity inputBound before path := by
  cases receipt.reads with
  | apply first query =>
      obtain ⟨middleStored, targetProfile, targetHeight, firstRequests, firstTrace, firstNodes, firstEdges⟩ :=
        force_receipt first ready known coherent member rows arity count depth bound stored profile lengthBound pathsBound heightBound
      obtain ⟨native, output, shaped, _leftHeight, rightHeight, queryRequests, queryTrace, queryCount, _nodeSupply, _edgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryActualNativeWork.counted
          (max (targetRows record rows count depth bound) inputRows) (max (max arity 1) inputArity) (max bound inputBound)
          query.actual first.ready.checked middleStored.native middleStored.output
          (NodeShape.mono _ targetProfile (Nat.le_max_left _ _) (Nat.le_max_left _ _))
          (NodeShape.mono _ inputProfile (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          (Nat.max_le.mpr ⟨Nat.le_trans targetHeight (Nat.le_max_left _ _), Nat.le_trans inputHeight (Nat.le_max_right _ _)⟩)
      refine ⟨SourceCurrentAllocatedFiniteOrdinarySharedProfiles.advance_stored _ _ middleStored native output,
        shaped, ⟨NodeShape.domain _ shaped, rightHeight⟩, Nat.le_trans rightHeight inputHeight,
        firstRequests ++ queryRequests, firstTrace.trans queryTrace, ?_, ?_⟩
      · rw [nodeRequests_append]
        unfold SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget
        change nodeRequests queryRequests + edgeRequests queryRequests ≤
          SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.queryBudget record rows arity count depth bound inputRows inputArity inputBound at queryCount
        omega
      · rw [edgeRequests_append]
        unfold SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget
        change nodeRequests queryRequests + edgeRequests queryRequests ≤
          SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.queryBudget record rows arity count depth bound inputRows inputArity inputBound at queryCount
        omega

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualSharedWork
