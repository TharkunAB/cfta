import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourceEqualityNativeDemandRunning

/-!
# Physical checked completion frames

Each finish split retains its actual physical check and full returned state.
Compiled bodies retain the exact evaluating owner until its own finish.
These helpers require no result language or structural result certificate.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {A : Type}

/-- A literal node finish exposes its current check and exact remaining physical trace. -/
theorem finishNode_split
    (fuel handle : Nat) (result : Value Symbol Guard) (next : Code Symbol Guard A)
    (before after : Checked width) (value : A)
    (trace : Trace fuel (.code (.finishNode handle result next)) before (.code (.pure value)) after) :
    ∃ rest, fuel = rest + 1 ∧ Inputs (.code (.finishNode handle result next)) before ∧
      Trace rest (.code next)
        {before with native := SourceRecursiveIntersectionThunks.finishNode handle result before.native}
        (.code (.pure value)) after := by
  have inputs := SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs trace
  obtain ⟨rest, total, tail⟩ := SourceCurrentAllocatedNativeSemanticTraceReadback.after_step fuel _ _ before _ after value
    trace (show step (.code (.finishNode handle result next)) before =
      .yielded (.code next)
        {before with native := SourceRecursiveIntersectionThunks.finishNode handle result before.native} from rfl)
  exact ⟨rest, total, inputs, tail⟩

/-- A literal edge finish exposes its current check and exact remaining physical trace. -/
theorem finishEdge_split
    (fuel handle : Nat) (result : EdgeValue Symbol Guard) (next : Code Symbol Guard A)
    (before after : Checked width) (value : A)
    (trace : Trace fuel (.code (.finishEdge handle result next)) before (.code (.pure value)) after) :
    ∃ rest, fuel = rest + 1 ∧ Inputs (.code (.finishEdge handle result next)) before ∧
      Trace rest (.code next)
        {before with native := SourceRecursiveIntersectionThunks.finishEdge handle result before.native}
        (.code (.pure value)) after := by
  have inputs := SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs trace
  obtain ⟨rest, total, tail⟩ := SourceCurrentAllocatedNativeSemanticTraceReadback.after_step fuel _ _ before _ after value
    trace (show step (.code (.finishEdge handle result next)) before =
      .yielded (.code next)
        {before with native := SourceRecursiveIntersectionThunks.finishEdge handle result before.native} from rfl)
  exact ⟨rest, total, inputs, tail⟩

/-- The actual compiled node body retains its evaluating owner before literal publication. -/
theorem node_body_cell
    (fuel handle : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width)
    (value : Value Symbol Guard)
    (trace : Trace fuel (.code (compileNode request)) before (.code (.pure value)) after)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩) :
    after.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishNode handle value after.native).nodes.cells handle =
        some ⟨request, .returned value⟩ := by
  have retained := SourceEqualityNativeDemandRunning.trace_retains fuel _ before after value trace.steps
    (SourceRecursiveIntersectionCode.compileNode_bodyCode request) valid.shape
  have present := retained.2.1 handle request running
  exact ⟨present, FlatMemoThunk.finish_evaluating handle value after.native.nodes request present⟩

/-- The actual checked edge body retains its evaluating owner before literal publication. -/
theorem edge_body_cell
    (fuel handle : Nat) (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (value : EdgeValue Symbol Guard)
    (trace : Trace fuel (.edgeBody request .pure) before (.code (.pure value)) after)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩) :
    after.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishEdge handle value after.native).edges.cells handle =
        some ⟨request, .returned value⟩ := by
  have retained := SourceEqualityNativeDemandRunning.trace_retains fuel _ before after value trace.steps
    (by intro result; trivial) valid.shape
  have present := retained.2.2 handle request running
  exact ⟨present, FlatMemoThunk.finish_evaluating handle value after.native.edges request present⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames

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
