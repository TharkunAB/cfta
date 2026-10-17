import MicroCFTA.SourceCurrentNativeWriterChildOrigins
import MicroCFTA.SourceCurrentNativeWriterReadyRetention

/-!
# Native row origins from a later checked reader

A completed edge call returns its exact captured cell. Actual later steps
retain that cell. The final reader history supplies its earlier writer.
This proof does not require history at an internal active node owner.
-/
namespace MicroCFTA.SourceCurrentNativeReaderRowLineage
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (Written History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeWriterReadyRetention (trace_retained)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual completed edge call returns its exact request and result cell. -/
theorem edge_returned {before after : Checked width}
    (input : EdgeRequest Symbol Guard) (fuel : Nat) (result : EdgeValue Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (requestEdge input.domain input.left input.right))
      before (.code (.pure result)) after) :
    ∃ handle, after.native.edges.cells handle = some ⟨input,.returned result⟩ := by
  cases actual with
  | cons _ _ resume reached _ _ rest inputs one tail =>
    cases selected : lookupEdge width input before.native with
    | mk handle chosen =>
      cases demanded : demandEdge handle chosen with
      | mk observation running =>
        cases observation with
        | absent | busy => simp only [step,requestEdge,selected,demanded] at one; cases one
        | ready value =>
          have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready input before.native chosen running handle value
            good.native inputs.1 inputs.2 selected demanded
          obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by simpa only [step,requestEdge,selected,demanded] using one)
          obtain ⟨rfl,rfl,rfl⟩ := pure_trace rest value result _ after tail.steps
          exact ⟨handle,by simpa only [receipt.2.1] using receipt.1⟩
        | evaluate original =>
          have originalSame := SourceCurrentAllocatedNativePhysicalCache.edge_started input original before.native chosen running handle
            good.native inputs.1 inputs.2 selected demanded
          subst original
          obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by simpa only [step,requestEdge,selected,demanded] using one)
          obtain ⟨inner,outer,value,current,_,bodyTrace,frameTrace⟩ := bind_inverse rest
            (.edgeBody input .pure) (fun value => .finishEdge handle value (.pure value))
            ⟨running,before.operations⟩ after result tail
          have chosenGood := SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid before.native good.native input inputs.1 inputs.2
          simp only [selected] at chosenGood
          have runningGood := SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid chosen chosenGood handle
          simp only [demanded] at runningGood
          have owner := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running input demanded).2
          have retained := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner inner handle input
            ⟨running,before.operations⟩ current value runningGood.shape owner bodyTrace.steps
          cases frameTrace with
          | cons _ _ next final _ _ count _ frameStep remaining =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
            obtain ⟨rfl,rfl,rfl⟩ := pure_trace count value result _ after remaining.steps
            exact ⟨handle,retained.2⟩

/-- A later reader recovers full row fields and historical ordered child calls from retained cells. -/
theorem rows_child {before after reader : Checked width} (history : History reader)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (rowSelected : (nodeEdges result)[rowIndex]? = some row)
    (childIndex : Nat) (value : Value Symbol Guard) (childSelected : row.children[childIndex]? = some value) :
    ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat)
        (leftChild rightChild : Value Symbol Guard) (callBefore callAfter : Checked width) (childFuel : Nat),
      left[leftIndex]? = some leftRow ∧ right[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      Written (width := width) handle ⟨domain,leftRow,rightRow⟩ row reader.native.machine.heap ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[childIndex]? = some leftChild ∧ rightRow.children[childIndex]? = some rightChild ∧
      Good callBefore ∧ Good callAfter ∧
      Grows callBefore.native.machine.heap reader.native.machine.heap ∧
      Grows callAfter.native.machine.heap reader.native.machine.heap ∧
      Trace childFuel (.code (requestNode domain leftChild rightChild)) callBefore (.code (.pure value)) callAfter := by
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
  obtain ⟨handle,stored⟩ := edge_returned ⟨domain,leftRow,rightRow⟩ edgeFuel row currentFacts.1 called
  have nextFacts := effects called currentFacts.1 (by intro value; trivial)
  have suffixRetained := trace_retained suffix.trace nextFacts.1.native.shape
  have madeRetained := trace_retained made middleFacts.1.native.shape
  have readerCell := (suffixRetained.trans (madeRetained.trans retained)).edges
    handle ⟨domain,leftRow,rightRow⟩ row stored
  have writer := history.writers handle ⟨domain,leftRow,rightRow⟩ row readerCell
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
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,symbol,guard⟩ := SourceCurrentNativeWriterChildOrigins.live writer survives
  obtain ⟨leftChild,rightChild,callBefore,callAfter,childFuel,leftChildFound,rightChildFound,
    callGood,afterGood,beforeGrowth,afterGrowth,childCall⟩ := SourceCurrentNativeWriterChildOrigins.child writer survives childIndex value childSelected
  exact ⟨leftIndex,rightIndex,leftRow,rightRow,handle,leftChild,rightChild,callBefore,callAfter,childFuel,
    leftFound,rightFound,symbols,writer,symbol,guard,leftChildFound,rightChildFound,
    callGood,afterGood,beforeGrowth,afterGrowth,childCall⟩

end MicroCFTA.SourceCurrentNativeReaderRowLineage
