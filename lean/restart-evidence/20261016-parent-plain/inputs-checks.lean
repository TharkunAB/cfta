import MicroCFTA.SourceCurrentAllocatedPartialPlainInputs
import MicroCFTA.SourceCurrentAllocatedLocalPlainRanges

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.own_empty
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.own_empty
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.children_member
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.children_member
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.rows_member
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.rows_member
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.node_evaluate
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.node_evaluate
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.edge_evaluate
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.edge_evaluate
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.edge_ready_shape
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainInputs.edge_ready_shape

namespace PlainInputsChecks
open MicroCFTA
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialPlainInputs
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Region" => SourceEqualityPartialPlainRegion.Region
local notation "Rows" => SourceEqualityPartialPlainRegion.Rows
local notation "Children" => SourceEqualityPartialPlainRegion.Children
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Sound" => SourceCurrentAllocatedPartialMemoSound.Sound
variable {width : Nat}

theorem physical_empty_iff (original : Guard) :
    SourceEqualityPhysicalPayload.own original = .ok (some []) ↔
      SourceCompactGuards.sourceEqualities original = some [] := by
  refine ⟨own_empty original, ?_⟩
  intro plain
  simp [SourceEqualityPhysicalPayload.own, plain, SourceEqualityPhysicalPayload.read,
    SourceEqualityClassOrder.recordsOf]

theorem original_row_supplies_parent_plan
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (budget : Nat) (edges : List Edge) (rows : Rows edges) (edge : Edge) (member : edge ∈ edges)
    (inherited : SourceEqualityConstraintAllocation.Value) (before : Caller width)
    (ready : SourceCurrentConjunctionClassScan.Ready before.checked)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : EqReady before.checked.operations.constraints inherited) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget ⟨inherited, edge⟩ before ∧
      ∀ child ∈ edge.children, Region child := by
  obtain ⟨empty, regions⟩ := rows_member rows edge member
  exact ⟨SourceCurrentAllocatedLocalPlainRanges.resident_ranges budget ⟨inherited, edge⟩ before ready resident
    inheritedReady (fun _ => empty), fun child member => children_member regions child member⟩

theorem node_owner_region_rank
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate owner : NodeRequest) (before running : Caller width) (handle : Nat)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints candidate.inherited)
    (available : Available before.checked.native.machine.heap candidate.value) (region : Region candidate.value)
    (started : beginNode candidate before = (handle, .evaluate owner, running)) :
    Region owner.value ∧ SourceCurrentAllocatedPartialActiveOrder.nodeRank owner =
      SourceCurrentAllocatedPartialActiveOrder.nodeRank candidate := by
  obtain ⟨same, transferred⟩ := node_evaluate formulas solver candidate owner before running handle
    sound coherent inheritedReady available region started
  exact ⟨transferred, by simp only [SourceCurrentAllocatedPartialActiveOrder.nodeRank, same]⟩

theorem edge_owner_row_rank
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate owner : EdgeRequest) (before running : Caller width) (handle : Nat)
    (edges : List Edge) (rows : Rows edges) (member : candidate.value ∈ edges)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints candidate.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap candidate.value)
    (started : beginEdge candidate before = (handle, .evaluate owner, running)) :
    SourceCompactGuards.sourceEqualities owner.value.entry.key.constraint = some [] ∧
      Children owner.value.children ∧ SourceCurrentAllocatedPartialActiveOrder.edgeRank owner =
        SourceCurrentAllocatedPartialActiveOrder.edgeRank candidate := by
  obtain ⟨plain, regions⟩ := rows_member rows candidate.value member
  obtain ⟨same, transferred, children⟩ := edge_evaluate formulas solver candidate owner before running handle
    sound coherent inheritedReady resident plain regions started
  exact ⟨transferred, children, by simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank, same]⟩

theorem ready_edge_child_region_rank
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : EdgeRequest) (before after : Caller width) (handle : Nat) (result : Edge)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap candidate.value)
    (domain : SourceCurrentAllocatedPartialReturnedDomain.Stored before)
    (regions : Children candidate.value.children)
    (started : beginEdge candidate before = (handle, .ready result, after))
    (inherited : SourceEqualityConstraintAllocation.Value) (child : Node) (member : child ∈ result.children) :
    after = before ∧ Region child ∧
      SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨inherited, child⟩ <
        SourceCurrentAllocatedPartialActiveOrder.edgeRank candidate := by
  obtain ⟨unchanged, shape⟩ := edge_ready_shape formulas solver candidate before after handle result
    sound coherent resident domain started
  have below := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge candidate.inherited inherited result child member
  have bounded := shape.height
  refine ⟨unchanged, shape.child_region regions child member, ?_⟩
  simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank] at below ⊢
  omega

end PlainInputsChecks

#print axioms PlainInputsChecks.physical_empty_iff
#check @PlainInputsChecks.physical_empty_iff
#print axioms PlainInputsChecks.original_row_supplies_parent_plan
#check @PlainInputsChecks.original_row_supplies_parent_plan
#print axioms PlainInputsChecks.node_owner_region_rank
#check @PlainInputsChecks.node_owner_region_rank
#print axioms PlainInputsChecks.edge_owner_row_rank
#check @PlainInputsChecks.edge_owner_row_rank
#print axioms PlainInputsChecks.ready_edge_child_region_rank
#check @PlainInputsChecks.ready_edge_child_region_rank
