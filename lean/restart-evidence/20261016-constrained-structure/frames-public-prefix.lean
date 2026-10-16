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

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.finishNode_split
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.finishNode_split
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.finishEdge_split
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.finishEdge_split
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.node_body_cell
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.node_body_cell
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.edge_body_cell
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames.edge_body_cell
