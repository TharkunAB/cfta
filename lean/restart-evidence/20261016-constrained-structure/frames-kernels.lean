import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames

namespace MicroCFTA.FiniteOrdinaryFramesReview
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

-- The actual finish reveals availability and installs the same owner at the same returned state.
theorem node_body_finish
    (bodyFuel finishFuel handle : Nat) (request : NodeRequest Symbol Guard)
    (before middle after : Checked width) (value result : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (body : Trace bodyFuel (.code (compileNode request)) before (.code (.pure value)) middle)
    (finish : Trace finishFuel (.code (.finishNode handle value (.pure value))) middle (.code (.pure result)) after) :
    value = result ∧ finishFuel = 1 ∧
      after = {middle with native := SourceRecursiveIntersectionThunks.finishNode handle value middle.native} ∧
      Available middle.native.machine.heap value ∧
      after.native.nodes.cells handle = some ⟨request, .returned result⟩ ∧
      after.native.machine = middle.native.machine ∧ after.operations = middle.operations ∧
      Trace (bodyFuel + finishFuel) (.code ((compileNode request).bind
        (fun output => .finishNode handle output (.pure output)))) before (.code (.pure result)) after := by
  have retained := SourceCurrentAllocatedFiniteOrdinaryFrames.node_body_cell bodyFuel handle request before middle value body valid running
  obtain ⟨rest, total, physical, tail⟩ := SourceCurrentAllocatedFiniteOrdinaryFrames.finishNode_split
    finishFuel handle value (.pure value) middle after result finish
  obtain ⟨owner, current, available⟩ := physical
  obtain ⟨rfl, rfl, rfl⟩ := pure_trace rest value result _ after tail.steps
  refine ⟨rfl, total, rfl, available, retained.2, rfl, rfl, ?_⟩
  exact (body.bind (fun output => .finishNode handle output (.pure output))).trans finish

-- Edge prefix allocation stays exact while the same edge owner reaches its physical finish.
theorem edge_body_finish
    (bodyFuel finishFuel handle : Nat) (request : EdgeRequest Symbol Guard)
    (before middle after : Checked width) (value result : EdgeValue Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (body : Trace bodyFuel (.edgeBody request .pure) before (.code (.pure value)) middle)
    (finish : Trace finishFuel (.code (.finishEdge handle value (.pure value))) middle (.code (.pure result)) after) :
    value = result ∧ finishFuel = 1 ∧
      after = {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle value middle.native} ∧
      EdgeResident middle.native.machine.heap value ∧
      after.native.edges.cells handle = some ⟨request, .returned result⟩ ∧
      after.native.machine = middle.native.machine ∧ after.operations = middle.operations := by
  have retained := SourceCurrentAllocatedFiniteOrdinaryFrames.edge_body_cell bodyFuel handle request before middle value body valid running
  obtain ⟨rest, total, physical, tail⟩ := SourceCurrentAllocatedFiniteOrdinaryFrames.finishEdge_split
    finishFuel handle value (.pure value) middle after result finish
  obtain ⟨owner, current, resident⟩ := physical
  obtain ⟨rfl, rfl, rfl⟩ := pure_trace rest value result _ after tail.steps
  exact ⟨rfl, total, rfl, resident, retained.2, rfl, rfl⟩
end MicroCFTA.FiniteOrdinaryFramesReview
#print axioms MicroCFTA.FiniteOrdinaryFramesReview.node_body_finish
#check @MicroCFTA.FiniteOrdinaryFramesReview.node_body_finish
#print axioms MicroCFTA.FiniteOrdinaryFramesReview.edge_body_finish
#check @MicroCFTA.FiniteOrdinaryFramesReview.edge_body_finish
