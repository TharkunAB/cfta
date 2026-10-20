import MicroCFTA.SourceCurrentNativeActiveQueryForwarding
import MicroCFTA.SourceCurrentNativePrefixWriterMaps
import MicroCFTA.SourceCurrentNativeWriterChildRetention
import MicroCFTA.SourceCurrentNativeReaderRowLineage

/-!
# Actual paired rows at an active reader

Each selected ordinary row retains both input row indices.
The same returned edge cell retains its actual historical writer.
Rows can have no children. No History at the reader is assumed.
-/
namespace MicroCFTA.SourceCurrentNativeActivePairedRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeForwardLineage (Forwarded)
open SourceRecursiveIntersectionControl (decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
private theorem ordinary_payload (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    SourceRecursiveIntersectionControl.payload request.left request.right = .ordinary := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact selected

private theorem ordinary_code [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    compileNode request = compileRows request.domain (nodeEdges request.left) (nodeEdges request.right) := by
  have payload := ordinary_payload request selected
  cases left : request.left <;> cases right : request.right <;>
    simp only [left,right,SourceRecursiveIntersectionControl.payload] at payload <;> try cases payload
  unfold compileNode
  simp only [selected]
  rw [left,right]
  rfl


/-- A selected row retains its paired source rows and the same edge writer. -/
def Joined (reader : Checked width) (request : NodeRequest Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat),
    (nodeEdges request.left)[leftIndex]? = some leftRow ∧
    (nodeEdges request.right)[rightIndex]? = some rightRow ∧
    leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
    reader.native.edges.cells handle = some ⟨⟨request.domain,leftRow,rightRow⟩,.returned row⟩ ∧
    SourceCurrentNativeEdgeWriterRetention.Written handle ⟨request.domain,leftRow,rightRow⟩ row reader.native ∧
    row.entry.key.symbol = leftRow.entry.key.symbol ∧
    row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
    Value.empty ∉ row.children

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem rows_writer {before after reader : Checked width} (writers : ∀ (handle : Nat) (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard),
      reader.native.edges.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeEdgeWriterRetention.Written handle request result reader.native)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (rowSelected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat),
      left[leftIndex]? = some leftRow ∧ right[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      reader.native.edges.cells handle = some ⟨⟨domain,leftRow,rightRow⟩,.returned row⟩ ∧
      SourceCurrentNativeEdgeWriterRetention.Written (width := width) handle ⟨domain,leftRow,rightRow⟩ row reader.native ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      Value.empty ∉ row.children := by
  obtain ⟨values,middle,count,walked,normalized,indexed⟩ := SourceCurrentNativeRowOrigins.rows
    domain left right fuel before after result good.native good.heap actual
  obtain ⟨inner,outer,rawValues,rawMiddle,_,first,made⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2) (pairs left right)))
    (fun values => .work (makeNode values) .pure) before after result actual
  have same : rawValues = values ∧ rawMiddle = middle := by
    have firstDone := done_stable (inner + 1) (count + 1) _ before rawMiddle rawValues
      (trace_done inner _ before rawMiddle rawValues first.steps)
    have secondDone := done_stable (count + 1) (inner + 1) _ before middle values
      (trace_done count _ before middle values walked.trace.steps)
    rw [Nat.add_comm (count + 1) (inner + 1)] at secondDone
    exact Outcome.done.inj (firstDone.symm.trans secondDone)
  rcases same with ⟨sameValues,sameMiddle⟩
  subst rawValues
  subst rawMiddle
  have walkFields := SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
    (pairs left right) (by intro pair member value; trivial)
  have middleFacts := effects walked.trace good walkFields
  obtain ⟨scheduleIndex,leftIndex,rightIndex,leftRow,rightRow,current,next,prefixFuel,edgeFuel,suffixFuel,
    found,_,leftFound,rightFound,symbols,_,initialCalls,called,suffix⟩ := indexed rowIndex row rowSelected
  have prefixFields := SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
    ((pairs left right).take scheduleIndex) (by intro pair member value; trivial)
  have currentFacts := effects initialCalls.trace good prefixFields
  obtain ⟨handle,stored⟩ := SourceCurrentNativeReaderRowLineage.edge_returned ⟨domain,leftRow,rightRow⟩ edgeFuel row currentFacts.1 called
  have nextFacts := effects called currentFacts.1 (by intro value; trivial)
  have suffixRetained := SourceCurrentNativeWriterReadyRetention.trace_retained suffix.trace nextFacts.1.native.shape
  have madeRetained := SourceCurrentNativeWriterReadyRetention.trace_retained made middleFacts.1.native.shape
  have readerCell := (suffixRetained.trans (madeRetained.trans retained)).edges
    handle ⟨domain,leftRow,rightRow⟩ row stored
  have writer := writers handle ⟨domain,leftRow,rightRow⟩ row readerCell
  have survives : Value.empty ∉ row.children := by
    have member : row ∈ canonicalEdges (surviving values) := by
      rw [normalized] at rowSelected
      exact List.mem_of_getElem? rowSelected
    have kept := (List.mem_filter.mp (canonicalEdges_member _ row member)).2
    intro emptyMember
    have anyEmpty : row.children.any (fun child => child.referenceOf == .empty) = true :=
      List.any_eq_true.mpr ⟨.empty,emptyMember,rfl⟩
    rw [anyEmpty] at kept
    cases kept
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,symbol,guard⟩ := SourceCurrentNativeWriterChildOrigins.live writer.forget survives
  exact ⟨leftIndex,rightIndex,leftRow,rightRow,handle,leftFound,rightFound,symbols,readerCell,writer,symbol,guard,survives⟩

/-- A supplied parent writer yields the same actual compiler interval and paired row. -/
theorem returned {reader : Checked width} (writers : ∀ (handle : Nat) (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard),
      reader.native.edges.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeEdgeWriterRetention.Written handle request result reader.native)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Node)
    (written : SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (ordinary : decision request.domain.key request.left request.right = .ordinary)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ (before after : Checked width) (fuel : Nat),
      Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
        {after with native := finishNode handle result after.native} ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
      Joined reader request row := by
  obtain ⟨before,after,fuel,good,ready,owner,body,kept,finish,first,last,retained⟩ := written
  have compiled := ordinary_code request ordinary
  have rows : Trace fuel (.code (compileRows request.domain (nodeEdges request.left) (nodeEdges request.right)))
      before (.code (.pure result)) after := compiled ▸ body
  have joined := rows_writer writers request.domain (nodeEdges request.left) (nodeEdges request.right)
    fuel result good rows retained rowIndex row selected
  exact ⟨before,after,fuel,good,ready,owner,body,kept,finish,first,last,retained,joined⟩

/-- An actual clean prefix derives both writer maps and the selected paired row. -/
theorem prefix {A : Type} (control final : Control A) (initial reader : Checked width) (count : Nat)
    (clean : Clean control) (good : Good initial) (fields : Fields control initial)
    (history : History initial) (actual : Trace count control initial final reader)
    (request : NodeRequest Symbol Guard) (result : Node) (handle : Nat)
    (cell : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (ordinary : decision request.domain.key request.left request.right = .ordinary)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Joined reader request row := by
  have maps := SourceCurrentNativePrefixWriterMaps.prefix control initial reader final count clean good fields history actual
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,joined⟩ := returned maps.2.1 handle request result
    (maps.1 handle request result cell) ordinary rowIndex row selected
  exact joined

end MicroCFTA.SourceCurrentNativeActivePairedRows
