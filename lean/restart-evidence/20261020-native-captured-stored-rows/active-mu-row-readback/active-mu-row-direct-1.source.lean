import MicroCFTA.SourceCurrentNativeActiveMuBodyOrigins
import MicroCFTA.SourceCurrentNativeMuWriterSourceRows
import MicroCFTA.SourceCurrentNativePrefixWriterMaps

/-!
# Mu row readback at an active reader

The supplied writer retains its same entered child and optional interval.
Actual reader publication history supplies readback and the body anchor.
An actual prefix extends its explicit initial publication history.
-/
namespace MicroCFTA.SourceCurrentNativeActiveMuRowReadback
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeForwardLineage (Forwarded)
open SourceCurrentNativeQueryMuRowOrigins (OptionalOrigin)
open SourceCurrentNativeMuWriterSourceRows (Anchor)
open SourceRecursiveIntersectionControl (decision identity pair)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem optional_origin (key : Nat × Nat) (bodyValue : Node) (before : Heap)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (available : Available before bodyValue) (result : Node) (after reader : Heap)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu key bodyValue before = .done result after)
    (publications : SourceCurrentNativeMuPublication.History empty reader) (growth : Grows after reader)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    OptionalOrigin key bodyValue before result after reader rowIndex row := by
  by_cases used : .intersection key.1 key.2 ∈ bodyValue.free
  · right
    refine ⟨used,?_⟩
    have constructed : SourceRecursiveIntersectionMaybeMu.construct (.intersection key.1 key.2)
        bodyValue before = .done result after := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_true] using actual
    exact SourceCurrentNativeConstructReaderReadback.construct_row _ bodyValue before semantic available
      result after constructed reader publications growth rowIndex row selected
  · left
    have same : InternedNestedConstruction.Outcome.done bodyValue before =
        (InternedNestedConstruction.Outcome.done result after : InternedNestedConstruction.Outcome Symbol Guard Node) := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_false] using actual
    obtain ⟨rfl,rfl⟩ := InternedNestedConstruction.Outcome.done.inj same
    exact ⟨used,rfl,rfl,selected⟩

/-- One selected writer retains its full actual Mu interval, optional row readback and body anchor. -/
def MuRow (reader : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Node) (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ (before after : Checked width) (fuel first second childFuel : Nat)
      (bodyValue : Node) (middle : Checked width) (heap : Heap),
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    let entry := {before with native := advance before.native {before.native.machine with domains := entered.2}}
    Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    identity request.left = some first ∧ identity request.right = some second ∧
    fuel = childFuel + 2 ∧ Good entry ∧
    Trace childFuel (.code (requestNode entered.1 (body request.left) (body request.right)))
      entry (.code (.pure bodyValue)) middle ∧ Good middle ∧
    Forwarded reader ⟨entered.1,body request.left,body request.right⟩ entry middle bodyValue ∧
    Available middle.native.machine.heap bodyValue ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue middle.native.machine.heap =
      .done result heap ∧
    after = {middle with native := advance middle.native {middle.native.machine with heap := heap}} ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
      {after with native := finishNode handle result after.native} ∧
    Grows before.native.machine.heap reader.native.machine.heap ∧
    Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
    OptionalOrigin (pair first second) bodyValue middle.native.machine.heap result heap
      reader.native.machine.heap rowIndex row ∧ Anchor bodyValue row

/-- The supplied strong writer derives readback without native History at the active reader. -/
theorem returned_mu {reader : Checked width}
    (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Node),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (publications : SourceCurrentNativeMuPublication.History empty reader.native.machine.heap)
    (request : NodeRequest Symbol Guard) (result : Node) (handle : Nat)
    (written : SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (branch : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    MuRow reader handle request result rowIndex row := by
  obtain ⟨before,after,fuel,good,ready,owner,actual,scheduled,kept,finish,firstGrowth,lastGrowth,retained⟩ :=
    SourceCurrentNativeActiveMuBodyOrigins.returned writers request result handle written branch
  obtain ⟨first,second,childFuel,bodyValue,middle,heap,firstId,secondId,count,
    entryGood,child,middleGood,forwarded,available,binder,final⟩ := scheduled
  have growth : Grows heap reader.native.machine.heap := by
    simpa only [final,advance] using lastGrowth
  have origin := optional_origin (pair first second) bodyValue middle.native.machine.heap middleGood.heap.semantic
    available result heap reader.native.machine.heap binder publications growth rowIndex row selected
  have anchor := SourceCurrentNativeMuWriterSourceRows.optional (pair first second) bodyValue
    middle.native.machine.heap middleGood.heap.semantic available result heap reader.native.machine.heap
    binder publications growth rowIndex row selected
  exact ⟨before,after,fuel,first,second,childFuel,bodyValue,middle,heap,good,ready,owner,actual,
    firstId,secondId,count,entryGood,child,middleGood,forwarded,available,binder,final,
    kept,finish,firstGrowth,lastGrowth,retained,origin,anchor⟩

/-- An actual clean prefix derives reader publication history and the same selected writer's Mu readback. -/
theorem «prefix» {A : Type} (control final : Control A) (initial reader : Checked width) (count : Nat)
    (clean : SourceEqualityNativeDemandBodyCode.Clean control) (good : Good initial)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control initial)
    (history : SourceCurrentNativeEdgeWriterGrowth.History initial)
    (publications : SourceCurrentNativeMuPublication.History empty initial.native.machine.heap)
    (actual : Trace count control initial final reader)
    (request : NodeRequest Symbol Guard) (result : Node) (handle : Nat)
    (cell : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (branch : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Nonempty (SourceCurrentNativeMuPublication.History empty reader.native.machine.heap) ∧
      MuRow reader handle request result rowIndex row := by
  have maps := SourceCurrentNativePrefixWriterMaps.prefix control initial reader final count clean good fields history actual
  obtain ⟨_,⟨published⟩⟩ := SourceCurrentNativePublicationTrace.from_history actual good.heap.semantic publications
  exact ⟨⟨published⟩,returned_mu maps.1 published request result handle
    (maps.1 handle request result cell) branch rowIndex row selected⟩

end MicroCFTA.SourceCurrentNativeActiveMuRowReadback
