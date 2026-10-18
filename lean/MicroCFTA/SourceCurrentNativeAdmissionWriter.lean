import MicroCFTA.SourceCurrentNativeKeyAdmission
import MicroCFTA.SourceCurrentSharedLeafNativeLineage

/-!
# Actual native writers from initial closed-request admission

Initial exact-key validity and source headroom produce the checked trace
of a literal completed closed request. Initial causal native history then
recovers its actual returned cell and earlier complete request writer.
No future trace, word range or returned-cell law is supplied. Initial
native history remains separate from target-slot history and weak cells.
-/
namespace MicroCFTA.SourceCurrentNativeAdmissionWriter
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial admission and causal history recover the actual completed closed request's captured writer. -/
theorem node_written (bits fuel : Nat) (before : Checked (bits + 2))
    (good : Good before) (history : History before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Node) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
        2 ^ (bits + 1))
    {result : Node} {after : Checked (bits + 2)}
    (actual : execute fuel (.code (requestNode emptyDomain left right)) before = .done result after) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      ∃ count, count < fuel ∧
        Trace count (.code (requestNode emptyDomain left right)) before (.code (.pure result)) after ∧
        ∃ handle, after.native.nodes.cells handle = some ⟨⟨emptyDomain,left,right⟩,.returned result⟩ ∧
          SourceCurrentNativeWriterReadyRetention.Written (width := bits + 2)
            handle ⟨emptyDomain,left,right⟩ result after.native := by
  obtain ⟨count,below,trace,_⟩ := SourceCurrentNativeKeyAdmission.node_done bits fuel before good semantic
    left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room actual
  obtain ⟨retained,final,growth,origin⟩ := SourceCurrentSharedLeafNativeLineage.request
    ⟨emptyDomain,left,right⟩ count result good history trace
  obtain ⟨handle,present,writer⟩ := origin.returned leftClosed rightClosed
  exact ⟨retained,final,growth,count,below,trace,handle,present,writer⟩

end MicroCFTA.SourceCurrentNativeAdmissionWriter
