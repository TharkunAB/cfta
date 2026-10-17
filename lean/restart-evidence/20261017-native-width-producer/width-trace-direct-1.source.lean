import MicroCFTA.SourceCurrentAllocatedNativeWidthStep

/-!
# Initial width production through actual native query traces

The initial code certificate produces every reached Work width check.
Actual physical extensions retain the certificate through native requests,
warm returns, and protected completion frames. Numeric store bounds follow
the same trace from its original source mass and instruction count.
No future width or intermediate store certificate is a public premise.
Complete query existence and an initial instruction count remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeWidthTrace
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields OutcomeFields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeWidthStep (ControlAt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "initialBound" => InternedValueMassHeap.initialBound
variable {width fuel bound : Nat} {A : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial code safety derives all reached widths and the final continuation certificate. -/
theorem widths {control next : Control A} {before after : Checked width}
    (actual : Trace fuel control before next after) (good : Good before) (fields : Fields control before)
    (stored : Stored bound before.native.machine.heap)
    (certificate : ControlAt control before bound post) :
    SourceCurrentAllocatedRecursiveMassTrace.InputsThrough fuel bound control before ∧
      ControlAt next after (massAfter fuel bound) post := by
  induction actual generalizing bound with
  | refl => exact ⟨trivial, certificate⟩
  | cons control before middle current next after count physical one rest ih =>
      have own := SourceCurrentAllocatedNativeWidthStep.inputs control before bound certificate
      have retained := SourceCurrentAllocatedNativeWidthStep.yielded_at control middle before current bound post
        good physical fields stored certificate one
      have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good physical fields
      have reached : Good current := by simpa only [one, Outcome.state] using effects.1
      have remaining : Fields middle current := by simpa only [one, OutcomeFields] using effects.2.2.2.2.2
      have currentStore : Stored (SourceCurrentAllocatedRecursiveMassTrace.ceiling bound) current.native.machine.heap := by
        have ownBound := SourceCurrentAllocatedRecursiveMassTrace.step_bound control before good physical stored own
        simpa only [one, Outcome.state] using ownBound.1
      obtain ⟨tail, final⟩ := ih reached remaining currentStore retained
      refine ⟨⟨own, ?_⟩, final⟩
      simpa only [one] using tail

/-- Every actual certified query prefix derives its numeric resources without future width premises. -/
theorem prefix {control next : Control A} {before after : Checked width}
    (actual : Trace fuel control before next after) (good : Good before) (fields : Fields control before)
    (stored : Stored bound before.native.machine.heap)
    (certificate : ControlAt control before bound post) :
    SourceCurrentAllocatedRecursiveMassTrace.InputsThrough fuel bound control before ∧
      ControlAt next after (massAfter fuel bound) post ∧ Good after ∧ Fields next after ∧
      Stored (massAfter fuel bound) after.native.machine.heap ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit fuel bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit fuel bound ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + fuel := by
  obtain ⟨produced, final⟩ := widths actual good fields stored certificate
  obtain ⟨lastGood, lastFields, lastStore, nodes, edges⟩ :=
    SourceCurrentAllocatedRecursiveMassTrace.prefix_bound actual good fields stored produced
  exact ⟨produced, final, lastGood, lastFields, lastStore, nodes, edges,
    SourceCurrentAllocatedRecursiveMassTrace.domain_prefix_bound actual⟩

/-- Original successful payload reads compute the initial bound for every actual certified prefix. -/
theorem initial {control next : Control A} {before after : Checked width}
    (actual : Trace fuel control before next after) (good : Good before) (fields : Fields control before)
    (certificate : ControlAt control before (initialBound before.native.machine.heap) post) :
    SourceCurrentAllocatedRecursiveMassTrace.InputsThrough fuel (initialBound before.native.machine.heap) control before ∧
      ControlAt next after (massAfter fuel (initialBound before.native.machine.heap)) post ∧ Good after ∧ Fields next after ∧
      Stored (massAfter fuel (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + fuel :=
  prefix actual good fields (InternedValueMassHeap.initial before.native.machine.heap good.native.machine.1) certificate

/-- An original node request derives every reached width and its final protected continuation. -/
theorem node_prefix (request : NodeRequest Symbol Guard) {next : Control (Value Symbol Guard)} {before after : Checked width}
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before next after)
    (good : Good before) (ready : NodeReady before.native.machine request) :
    SourceCurrentAllocatedRecursiveMassTrace.InputsThrough fuel (initialBound before.native.machine.heap)
      (.code (requestNode request.domain request.left request.right)) before ∧
      ControlAt next after (massAfter fuel (initialBound before.native.machine.heap)) (fun final value => Available final.heap value) ∧
      Good after ∧ Fields next after ∧ Stored (massAfter fuel (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + fuel := by
  exact initial actual good (fun _ => trivial)
    (SourceRecursiveIntersectionCodeMass.request_node request.domain request.left request.right before.native.machine _ ready)

/-- An original edge request derives every reached width through either checked body branch. -/
theorem edge_prefix (request : EdgeRequest Symbol Guard) {next : Control (EdgeValue Symbol Guard)} {before after : Checked width}
    (actual : Trace fuel (.code (requestEdge request.domain request.left request.right)) before next after)
    (good : Good before) (ready : EdgeReady before.native.machine request) :
    SourceCurrentAllocatedRecursiveMassTrace.InputsThrough fuel (initialBound before.native.machine.heap)
      (.code (requestEdge request.domain request.left request.right)) before ∧
      ControlAt next after (massAfter fuel (initialBound before.native.machine.heap)) (fun final edge => EdgeResident final.heap edge) ∧
      Good after ∧ Fields next after ∧ Stored (massAfter fuel (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + fuel := by
  exact initial actual good (fun _ => trivial)
    (SourceRecursiveIntersectionCodeMass.request_edge request.domain request.left request.right before.native.machine _ ready)

/-- A completed actual node trace derives its own result mass and numeric headroom from the original heap. -/
theorem node_return (request : NodeRequest Symbol Guard) {before after : Checked width} (value : Value Symbol Guard)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after)
    (good : Good before) (ready : NodeReady before.native.machine request) :
    execute (fuel + 1) (.code (requestNode request.domain request.left request.right)) before = .done value after ∧
      Stored (massAfter fuel (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      InternedValueMass.value value ≤ massAfter fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + fuel := by
  obtain ⟨_widths, available, _good, _fields, stored, nodes, edges, domains⟩ := node_prefix request actual good ready
  exact ⟨trace_done _ _ _ _ _ actual.steps, stored,
    InternedValueMassHeap.available after.native.machine.heap stored value available, nodes, edges, domains⟩

/-- A completed actual edge trace derives its own row mass and numeric headroom from the original heap. -/
theorem edge_return (request : EdgeRequest Symbol Guard) {before after : Checked width} (value : EdgeValue Symbol Guard)
    (actual : Trace fuel (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after)
    (good : Good before) (ready : EdgeReady before.native.machine request) :
    execute (fuel + 1) (.code (requestEdge request.domain request.left request.right)) before = .done value after ∧
      Stored (massAfter fuel (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      InternedValueMass.edge value ≤ massAfter fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit fuel (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + fuel := by
  obtain ⟨_widths, resident, _good, _fields, stored, nodes, edges, domains⟩ := edge_prefix request actual good ready
  exact ⟨trace_done _ _ _ _ _ actual.steps, stored,
    InternedValueMassHeap.resident after.native.machine.heap stored value resident, nodes, edges, domains⟩

end MicroCFTA.SourceCurrentAllocatedNativeWidthTrace
