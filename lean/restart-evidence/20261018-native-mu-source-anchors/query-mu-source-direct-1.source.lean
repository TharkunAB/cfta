import MicroCFTA.SourceCurrentNativeMuWriterSourceRows

/-!
# Original generated-body rows at actual terminal Mu writers

Closed forwarding retains every terminal branch. The Mu branch adds an
indexed original transition of its actual child result before rebinding.
That child result can be generated. This is not an initial operand anchor.
-/
namespace MicroCFTA.SourceCurrentNativeQueryMuSourceRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeQueryRowOrigins (Route Joined)
open SourceCurrentNativeQueryTerminalOrigins (Union)
open SourceCurrentNativeMuWriterSourceRows (MuRow)
open SourceRecursiveIntersectionControl (decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Closed terminal rows retain every branch and actual Mu body transition anchors. -/
def Resolved (reader : Checked width) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ terminal handle, Route reader result request terminal ∧
    terminal.left.free = [] ∧ terminal.right.free = [] ∧
    reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
    SourceCurrentNativeWriterReadyRetention.Written (width := width) handle terminal result reader.native ∧
    ((decision terminal.domain.key terminal.left terminal.right = .self ∧
        (nodeEdges terminal.left)[rowIndex]? = some row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .ordinary ∧ Joined reader terminal row) ∨
     ((decision terminal.domain.key terminal.left terminal.right = .bothMu ∨
       decision terminal.domain.key terminal.left terminal.right = .leftMu ∨
       decision terminal.domain.key terminal.left terminal.right = .rightMu) ∧ MuRow reader handle terminal result rowIndex row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .leftUnion ∧ Union true reader handle terminal result row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .rightUnion ∧ Union false reader handle terminal result row))

/-- An actual returned closed query derives the full classification with generated-body transition anchors. -/
theorem returned {reader : Checked width} (history : History reader)
    (publications : SourceCurrentNativeMuPublication.History empty reader.native.machine.heap)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : request.left.free = []) (right : request.right.free = [])
    (handle : Nat) (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Resolved reader request result rowIndex row := by
  obtain ⟨terminal,owner,route,closedLeft,closedRight,cell,writer,cases⟩ :=
    SourceCurrentNativeQueryMuRowOrigins.returned history publications request result left right handle present rowIndex row selected
  refine ⟨terminal,owner,route,closedLeft,closedRight,cell,writer,?_⟩
  rcases cases with self | ordinary | mu | leftUnion | rightUnion
  · exact .inl self
  · exact .inr (.inl ordinary)
  · exact .inr (.inr (.inl ⟨mu.1,SourceCurrentNativeMuWriterSourceRows.returned_mu
      history publications terminal result owner cell mu.1 rowIndex row selected⟩))
  · exact .inr (.inr (.inr (.inl leftUnion)))
  · exact .inr (.inr (.inr (.inr rightUnion)))

/-- Initial publication history and an actual query trace derive terminal row sources at the final reader. -/
theorem request {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before) (history : History before)
    (publications : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)
    (left : input.left.free = []) (right : input.right.free = [])
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) ∧
      Resolved after input result rowIndex row := by
  obtain ⟨_,⟨published⟩⟩ := SourceCurrentNativePublicationTrace.from_history actual good.heap.semantic publications
  obtain ⟨reached,checked,growth,origin⟩ := SourceCurrentSharedLeafNativeLineage.request input fuel result good history actual
  obtain ⟨handle,present,_⟩ := origin.returned left right
  exact ⟨reached,checked,growth,⟨published⟩,returned reached published input result left right handle present rowIndex row selected⟩

end MicroCFTA.SourceCurrentNativeQueryMuSourceRows
