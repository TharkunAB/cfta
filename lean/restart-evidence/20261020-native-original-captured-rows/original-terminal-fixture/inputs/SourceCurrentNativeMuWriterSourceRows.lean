import MicroCFTA.SourceCurrentNativeQueryMuRowOrigins
import MicroCFTA.SourceCurrentNativeConstructSourceRows

/-!
# Original body rows of actual native Mu writers

The source anchor belongs to the captured writer's actual generated body.
The receipt retains that same writer and its exact child trace.
-/
namespace MicroCFTA.SourceCurrentNativeMuWriterSourceRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceRecursiveIntersectionControl (identity pair)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentNativeQueryMuRowOrigins (OptionalOrigin)

/-- A complete row retains an original body occurrence, full fields, and actual ordered child calls. -/
def Anchor [DecidableEq (EdgeKey Symbol Guard)] (bodyValue : Value Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  ∃ original, RowAt bodyValue original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
    row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
    (row = original ∨ ∃ lexical before after, Calls lexical original.children before row.children after)

/-- An actual optional binder derives a source anchor from its unchanged body or actual reconstruction. -/
theorem optional [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (bodyValue : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (available : Available before bodyValue) (result : Value Symbol Guard) (after reader : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu key bodyValue before = .done result after)
    (publications : SourceCurrentNativeMuPublication.History empty reader) (growth : Grows after reader)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Anchor bodyValue row := by
  by_cases used : .intersection key.1 key.2 ∈ bodyValue.free
  · have constructed : SourceRecursiveIntersectionMaybeMu.construct (.intersection key.1 key.2)
        bodyValue before = .done result after := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_true] using actual
    exact SourceCurrentNativeConstructSourceRows.construct _ bodyValue before semantic available result after
      constructed reader publications growth rowIndex row selected
  · have same : InternedNestedConstruction.Outcome.done bodyValue before =
        (InternedNestedConstruction.Outcome.done result after : InternedNestedConstruction.Outcome Symbol Guard (Value Symbol Guard)) := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_false] using actual
    obtain ⟨rfl,rfl⟩ := InternedNestedConstruction.Outcome.done.inj same
    cases bodyValue with
    | node entry rows level free => exact ⟨row,.node selected,rfl,rfl,rfl,Or.inl rfl⟩
    | empty | reference | union | mu => simp only [nodeEdges,List.getElem?_nil] at selected; cases selected

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]

/-- A selected Mu row retains one exact captured writer, optional readback, and original generated-body anchor. -/
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
      reader.native.machine.heap rowIndex row ∧ Anchor bodyValue row

/-- An actual returned Mu cell derives the source anchor at the same captured writer and body trace. -/
theorem returned_mu {reader : Checked width} (history : History reader)
    (publications : SourceCurrentNativeMuPublication.History empty reader.native.machine.heap)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (handle : Nat)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    MuRow reader handle request result rowIndex row := by
  obtain ⟨before,after,fuel,first,second,childFuel,bodyValue,middle,heap,good,ready,owner,actual,
    firstId,secondId,count,child,available,binder,final,kept,firstGrowth,lastGrowth,retained,origin⟩ :=
    SourceCurrentNativeQueryMuRowOrigins.returned_mu history publications request result handle present branch
      rowIndex row selected
  have semantic := (SourceCurrentNativePublicationTrace.trace child good.heap.semantic).1
  have growth : Grows heap reader.native.machine.heap := by
    simpa only [final,advance] using lastGrowth
  have anchor := optional (pair first second) bodyValue middle.native.machine.heap semantic available
    result heap reader.native.machine.heap binder publications growth rowIndex row selected
  exact ⟨before,after,fuel,first,second,childFuel,bodyValue,middle,heap,good,ready,owner,actual,
    firstId,secondId,count,child,available,binder,final,kept,firstGrowth,lastGrowth,retained,origin,anchor⟩

end MicroCFTA.SourceCurrentNativeMuWriterSourceRows
