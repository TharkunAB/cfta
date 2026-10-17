import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCache
import MicroCFTA.SourceCurrentConstrainedCapNativeTraceGlue

/-!
# Ranked publication from the same actual smaller body

The physical receipt retains the literal complete body and checked state.
Its local induction result supplies the universal cap law and the fixed-source
occurrence law. The captured finish installs both laws at that exact owner.
This module does not derive the missing joint native compiler induction.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceTrace
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapNativeLaws (NodeLaw EdgeLaw)
open SourceCurrentAllocatedRecursivePrefixState (Current)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "Receipt" => SourceCurrentConstrainedCapNativeTraceGlue.Receipt
local notation "Ranked" => SourceCurrentConstrainedCapNativeOccurrenceCache.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {annotation : Guard → Prop} {source : State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- The actual node finish retains its smaller body's cap and ranked laws at the exact captured owner. -/
theorem finish_node {fuel handle : Nat} (request : NodeRequest Symbol Guard) {before middle : Checked width}
    {value : Value Symbol Guard} (known : Current source inventory initial before)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (body : Receipt annotation source inventory initial fuel (.code (compileNode request)) before value middle
      (fun state value => Available state.heap value)
      (fun _ value => (∀ scope, NodeLaw annotation scope request value) ∧
        SourceCurrentConstrainedCapNativeOccurrenceCache.NodeLaw annotation source request value))
    (ranked : Ranked annotation source middle.native) :
    Receipt annotation source inventory initial (fuel + 1)
        ((.code (compileNode request) : Control (Value Symbol Guard)).bind (fun value => .finishNode handle value (.pure value)))
        before value {middle with native := finishNode handle value middle.native}
        (fun state value => Available state.heap value)
        (fun _ value => (∀ scope, NodeLaw annotation scope request value) ∧
          SourceCurrentConstrainedCapNativeOccurrenceCache.NodeLaw annotation source request value) ∧
      Ranked annotation source (finishNode handle value middle.native) ∧
      (finishNode handle value middle.native).nodes.cells handle = some ⟨request, .returned value⟩ := by
  have capped : Receipt annotation source inventory initial fuel (.code (compileNode request)) before value middle
      (fun state value => Available state.heap value) (fun _ value => ∀ scope, NodeLaw annotation scope request value) :=
    ⟨body.physical, body.stored, body.result.1⟩
  have actual := SourceCurrentConstrainedCapNativeTraceGlue.finish_node request known running capped
  have owner := SourceEqualityNativeDemandProtectedPrefix.node_body_owner fuel handle request before middle value
    known.good.native.shape running body.physical.trace.steps
  have retained := SourceCurrentConstrainedCapNativeOccurrenceCache.finishNode_stored annotation source
    middle.native handle request value body.physical.current.good.native ranked owner.1
    (body.result.1 source) body.result.2
  exact ⟨⟨actual.1.physical, actual.1.stored, body.result⟩, retained, actual.2⟩

/-- The checked row body retains both exact local laws through its literal captured finish. -/
theorem finish_edge {fuel handle : Nat} (request : EdgeRequest Symbol Guard) {before middle : Checked width}
    {value : EdgeValue Symbol Guard} (known : Current source inventory initial before)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (body : Receipt annotation source inventory initial fuel (.edgeBody request .pure) before value middle
      (fun state value => EdgeResident state.heap value)
      (fun _ value => (∀ scope, EdgeLaw annotation scope request value) ∧
        SourceCurrentConstrainedCapNativeOccurrenceCache.EdgeLaw annotation source request value))
    (ranked : Ranked annotation source middle.native) :
    Receipt annotation source inventory initial (fuel + 1)
        ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind (fun value => .finishEdge handle value (.pure value)))
        before value {middle with native := finishEdge handle value middle.native}
        (fun state value => EdgeResident state.heap value)
        (fun _ value => (∀ scope, EdgeLaw annotation scope request value) ∧
          SourceCurrentConstrainedCapNativeOccurrenceCache.EdgeLaw annotation source request value) ∧
      Ranked annotation source (finishEdge handle value middle.native) ∧
      (finishEdge handle value middle.native).edges.cells handle = some ⟨request, .returned value⟩ := by
  have capped : Receipt annotation source inventory initial fuel (.edgeBody request .pure) before value middle
      (fun state value => EdgeResident state.heap value) (fun _ value => ∀ scope, EdgeLaw annotation scope request value) :=
    ⟨body.physical, body.stored, body.result.1⟩
  have actual := SourceCurrentConstrainedCapNativeTraceGlue.finish_edge request known running capped
  have owner := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner fuel handle request before middle value
    known.good.native.shape running body.physical.trace.steps
  have retained := SourceCurrentConstrainedCapNativeOccurrenceCache.finishEdge_stored annotation source
    middle.native handle request value body.physical.current.good.native ranked owner.1
    (body.result.1 source) body.result.2
  exact ⟨⟨actual.1.physical, actual.1.stored, body.result⟩, retained, actual.2⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceTrace
