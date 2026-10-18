import MicroCFTA.SourceCurrentNativeQueryTerminalOrigins
import MicroCFTA.SourceCurrentNativeConstructReaderReadback
import MicroCFTA.SourceCurrentNativePublicationTrace

/-!
# Actual Mu row readback at the final query reader

The captured writer retains its body and literal binder outcome.
The actual stored winner grows forward to the final reader.
That reader's causal publication history supplies the unused cleanup law.
No publication history is inferred backwards at a prior compiler state.
-/
namespace MicroCFTA.SourceCurrentNativeQueryMuRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeQueryRowOrigins (Route Joined)
open SourceCurrentNativeQueryTerminalOrigins (Union)
open SourceRecursiveIntersectionControl (decision identity pair)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A selected optional-binder row is unchanged or comes from the actual ordinary substitution. -/
def OptionalOrigin (key : Nat × Nat) (bodyValue : Value Symbol Guard) (before : Heap)
    (result : Value Symbol Guard) (after reader : Heap) (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ((.intersection key.1 key.2 ∉ bodyValue.free) ∧ result = bodyValue ∧ after = before ∧
      (nodeEdges bodyValue)[rowIndex]? = some row) ∨
  ((.intersection key.1 key.2 ∈ bodyValue.free) ∧
    SourceCurrentNativeConstructReaderReadback.RowReadback (.intersection key.1 key.2)
      bodyValue before result after reader rowIndex row)

private theorem optional (key : Nat × Nat) (bodyValue : Value Symbol Guard) (before : Heap)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (available : Available before bodyValue) (result : Value Symbol Guard) (after reader : Heap)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu key bodyValue before = .done result after)
    (history : SourceCurrentNativeMuPublication.History empty reader) (growth : Grows after reader)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    OptionalOrigin key bodyValue before result after reader rowIndex row := by
  by_cases used : .intersection key.1 key.2 ∈ bodyValue.free
  · right
    refine ⟨used,?_⟩
    have constructed : SourceRecursiveIntersectionMaybeMu.construct (.intersection key.1 key.2)
        bodyValue before = .done result after := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_true] using actual
    exact SourceCurrentNativeConstructReaderReadback.construct_row _ bodyValue before semantic available
      result after constructed reader history growth rowIndex row selected
  · left
    have same : InternedNestedConstruction.Outcome.done bodyValue before =
        (InternedNestedConstruction.Outcome.done result after : InternedNestedConstruction.Outcome Symbol Guard (Value Symbol Guard)) := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_false] using actual
    obtain ⟨rfl,rfl⟩ := InternedNestedConstruction.Outcome.done.inj same
    exact ⟨used,rfl,rfl,selected⟩

variable [DecidableEq Symbol]

/-- A selected Mu row retains one actual body trace and its exact optional-binder row readback. -/
def MuRow (reader : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Value Symbol Guard) (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ (before after : Checked width) (fuel first second childFuel : Nat)
      (bodyValue : Value Symbol Guard) (middle : Checked width) (heap : Heap),
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    identity request.left = some first ∧ identity request.right = some second ∧
    fuel = childFuel + 2 ∧
    Trace childFuel (.code (requestNode entered.1 (body request.left) (body request.right)))
      {before with native := advance before.native {before.native.machine with domains := entered.2}}
      (.code (.pure bodyValue)) middle ∧
    Available middle.native.machine.heap bodyValue ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue middle.native.machine.heap =
      .done result heap ∧
    after = {middle with native := advance middle.native {middle.native.machine with heap := heap}} ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Grows before.native.machine.heap reader.native.machine.heap ∧
    Grows after.native.machine.heap reader.native.machine.heap ∧
    SourceEqualityNativeDemandMemo.Retained after.native reader.native ∧
    OptionalOrigin (pair first second) bodyValue middle.native.machine.heap result heap
      reader.native.machine.heap rowIndex row

/-- The captured Mu writer derives row reconstruction from the final reader's actual publication history. -/
theorem returned_mu {reader : Checked width} (history : History reader)
    (publications : SourceCurrentNativeMuPublication.History empty reader.native.machine.heap)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (handle : Nat)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (branch : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    MuRow reader handle request result rowIndex row := by
  obtain ⟨before,after,fuel,good,ready,owner,actual,scheduled,kept,firstGrowth,lastGrowth,retained⟩ :=
    SourceCurrentNativeMuWriterOrigins.returned history request result handle present branch
  obtain ⟨first,second,childFuel,bodyValue,middle,heap,firstId,secondId,count,child,available,binder,final,_unused⟩ := scheduled
  have semantic := (SourceCurrentNativePublicationTrace.trace child good.heap.semantic).1
  have growth : Grows heap reader.native.machine.heap := by
    simpa only [final,advance] using lastGrowth
  have origin := optional (pair first second) bodyValue middle.native.machine.heap semantic available
    result heap reader.native.machine.heap binder publications growth rowIndex row selected
  exact ⟨before,after,fuel,first,second,childFuel,bodyValue,middle,heap,good,ready,owner,actual,
    firstId,secondId,count,child,available,binder,final,kept,firstGrowth,lastGrowth,retained,origin⟩

/-- Every closed selected row has an exact terminal writer and an explicit supported branch origin. -/
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

/-- Each actual closed returned query derives row reconstruction at its terminal Mu writer. -/
theorem returned {reader : Checked width} (history : History reader)
    (publications : SourceCurrentNativeMuPublication.History empty reader.native.machine.heap)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : request.left.free = []) (right : request.right.free = [])
    (handle : Nat) (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Resolved reader request result rowIndex row := by
  obtain ⟨terminal,owner,route,closedLeft,closedRight,cell,writer,cases⟩ :=
    SourceCurrentNativeQueryTerminalOrigins.returned history request result left right handle present rowIndex row selected
  refine ⟨terminal,owner,route,closedLeft,closedRight,cell,writer,?_⟩
  rcases cases with self | ordinary | mu | leftUnion | rightUnion
  · exact .inl self
  · exact .inr (.inl ordinary)
  · exact .inr (.inr (.inl ⟨mu.1,returned_mu history publications terminal result owner cell mu.1 rowIndex row selected⟩))
  · exact .inr (.inr (.inr (.inl leftUnion)))
  · exact .inr (.inr (.inr (.inr rightUnion)))

/-- Initial causal publication history and an actual query trace derive the full row classification. -/
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

end MicroCFTA.SourceCurrentNativeQueryMuRowOrigins
