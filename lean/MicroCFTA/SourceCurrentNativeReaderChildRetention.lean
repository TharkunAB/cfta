import MicroCFTA.SourceCurrentNativeWriterChildRetention
import MicroCFTA.SourceCurrentNativeOriginViewBranches
import MicroCFTA.SourceCurrentNativeWriterReadyRetention

/-!
# Returned native children from a captured reader

A selected surviving row retains its earlier edge writer and actual child
call. Native retention connects that child return to the checked reader.
The reader history supplies the exact child returned cell and writer.
-/
namespace MicroCFTA.SourceCurrentNativeReaderChildRetention
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeEdgeWriterRetention (Written)
open MergedFreshOrdinaryGraph (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeWriterReadyRetention (trace_retained)
private theorem ordinary_payload (request : NodeRequest Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary) :
    SourceRecursiveIntersectionControl.payload request.left request.right = .ordinary := by
  unfold SourceRecursiveIntersectionControl.decision at selected
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

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]


/-- A selected surviving row derives its actual child call and returned writer at the same reader. -/
theorem rows_returned {before after reader : Checked width} (history : History reader)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (rowSelected : (nodeEdges result)[rowIndex]? = some row)
    (childIndex : Nat) (value : Value Symbol Guard) (childSelected : row.children[childIndex]? = some value) :
    ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat)
        (leftChild rightChild : Value Symbol Guard) (callBefore callAfter : Checked width) (childFuel childHandle : Nat),
      left[leftIndex]? = some leftRow ∧ right[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      Written (width := width) handle ⟨domain,leftRow,rightRow⟩ row reader.native ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[childIndex]? = some leftChild ∧ rightRow.children[childIndex]? = some rightChild ∧
      Good callBefore ∧ Good callAfter ∧
      Grows callBefore.native.machine.heap reader.native.machine.heap ∧
      Grows callAfter.native.machine.heap reader.native.machine.heap ∧
      Trace childFuel (.code (requestNode domain leftChild rightChild)) callBefore (.code (.pure value)) callAfter ∧
      Retained callAfter.native reader.native ∧
      SourceCurrentNativeForwardLineage.Forwarded reader ⟨domain,leftChild,rightChild⟩ callBefore callAfter value ∧
      reader.native.nodes.cells childHandle = some ⟨⟨domain,leftChild,rightChild⟩,.returned value⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) childHandle
        ⟨domain,leftChild,rightChild⟩ value reader.native := by
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
  have suffixRetained := trace_retained suffix.trace nextFacts.1.native.shape
  have madeRetained := trace_retained made middleFacts.1.native.shape
  have readerCell := (suffixRetained.trans (madeRetained.trans retained)).edges
    handle ⟨domain,leftRow,rightRow⟩ row stored
  have writer := SourceCurrentNativeEdgeWriterRetention.edge_writers history handle ⟨domain,leftRow,rightRow⟩ row readerCell
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
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,symbol,guard,_⟩ := SourceCurrentNativeWriterChildRetention.live writer survives
  obtain ⟨leftChild,rightChild,callBefore,callAfter,childFuel,childHandle,leftChildFound,rightChildFound,
    callGood,afterGood,beforeGrowth,afterGrowth,childCall,childRetained,forwarded,childCell,childWriter⟩ :=
    SourceCurrentNativeWriterChildRetention.returned history writer survives childIndex value childSelected
  exact ⟨leftIndex,rightIndex,leftRow,rightRow,handle,leftChild,rightChild,callBefore,callAfter,childFuel,childHandle,
    leftFound,rightFound,symbols,writer,symbol,guard,leftChildFound,rightChildFound,
    callGood,afterGood,beforeGrowth,afterGrowth,childCall,childRetained,forwarded,childCell,childWriter⟩

/-- An ordinary origin derives its returned child writer and both strict original child masses. -/
theorem ordinary {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (view : Heap) (row : EdgeValue Symbol Guard) (origin : Origin view [result] row)
    (childIndex : Nat) (value : Value Symbol Guard) (chosen : row.children[childIndex]? = some value) :
    ∃ (rowIndex leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (edgeHandle : Nat)
        (leftChild rightChild : Value Symbol Guard) (before after : Checked width) (fuel childHandle : Nat),
      (nodeEdges result)[rowIndex]? = some row ∧
      (nodeEdges request.left)[leftIndex]? = some leftRow ∧
      (nodeEdges request.right)[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      Written (width := width) edgeHandle ⟨request.domain,leftRow,rightRow⟩ row reader.native ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[childIndex]? = some leftChild ∧ rightRow.children[childIndex]? = some rightChild ∧
      InternedValueMass.value leftChild < InternedValueMass.value request.left ∧
      InternedValueMass.value rightChild < InternedValueMass.value request.right ∧
      Good before ∧ Good after ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧ Grows after.native.machine.heap reader.native.machine.heap ∧
      Trace fuel (.code (requestNode request.domain leftChild rightChild)) before (.code (.pure value)) after ∧
      Retained after.native reader.native ∧
      SourceCurrentNativeForwardLineage.Forwarded reader ⟨request.domain,leftChild,rightChild⟩ before after value ∧
      reader.native.nodes.cells childHandle = some ⟨⟨request.domain,leftChild,rightChild⟩,.returned value⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) childHandle
        ⟨request.domain,leftChild,rightChild⟩ value reader.native := by
  obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result present
  have payload := ordinary_payload request branch
  cases left : request.left <;> cases right : request.right <;>
    simp only [left,right,SourceRecursiveIntersectionControl.payload] at payload <;> try cases payload
  rename_i leftEntry leftRows leftDepth leftFree rightEntry rightRows rightDepth rightFree
  rw [←left,←right]
  have compiled : compileNode request = compileRows request.domain (nodeEdges request.left) (nodeEdges request.right) := by
    unfold compileNode
    simp only [branch]
    rw [left,right]
    rfl
  have body := compiled ▸ actual
  obtain ⟨index,_,_,_,_,_,_,_,_,_,_,selected,_⟩ :=
    SourceCurrentNativeOriginViewBranches.ordinary history handle request result present branch view row origin childIndex value chosen
  obtain ⟨firstIndex,secondIndex,firstRow,secondRow,edge,firstChild,secondChild,current,next,count,childHandle,
      firstFound,secondFound,symbols,written,symbol,guard,firstSelected,secondSelected,
      initial,final,firstGrowth,lastGrowth,called,childRetained,forwarded,childCell,childWriter⟩ :=
    rows_returned history request.domain (nodeEdges request.left) (nodeEdges request.right)
      fuel result good body retained index row selected childIndex value chosen
  have firstMass : InternedValueMass.value firstChild < InternedValueMass.value request.left := by
    rw [left]
    exact InternedValueMass.node_child_lt leftEntry leftRows leftDepth leftFree firstRow
      (by simpa only [left,nodeEdges] using List.mem_of_getElem? firstFound) firstChild (List.mem_of_getElem? firstSelected)
  have secondMass : InternedValueMass.value secondChild < InternedValueMass.value request.right := by
    rw [right]
    exact InternedValueMass.node_child_lt rightEntry rightRows rightDepth rightFree secondRow
      (by simpa only [right,nodeEdges] using List.mem_of_getElem? secondFound) secondChild (List.mem_of_getElem? secondSelected)
  exact ⟨index,firstIndex,secondIndex,firstRow,secondRow,edge,firstChild,secondChild,current,next,count,childHandle,
    selected,firstFound,secondFound,symbols,written,symbol,guard,firstSelected,secondSelected,
    firstMass,secondMass,initial,final,firstGrowth,lastGrowth,called,childRetained,forwarded,childCell,childWriter⟩

end MicroCFTA.SourceCurrentNativeReaderChildRetention
