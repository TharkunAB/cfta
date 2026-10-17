import MicroCFTA.SourceCurrentNativeReaderRowLineage
import MicroCFTA.SourceCurrentNativeForwardLineage
import MicroCFTA.SourceCurrentSharedLeafNativeLineage
import MicroCFTA.SourceRecursiveIntersectionSchedule

/-!
# Root query row origins after actual native forwarding

The final reader history supplies each earlier captured writer. Actual
swap and reset bodies lead to a terminal captured request. A selected row
then has a literal self origin, a joined ordinary-row origin, or an
explicit recursive, union, or reference exposure obligation.
-/
namespace MicroCFTA.SourceCurrentNativeQueryRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History Written)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionControl (decision reset greater)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A joined row retains both original indices, full fields, and its actual writer. -/
def Joined (reader : Checked width) (request : NodeRequest Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat),
    (nodeEdges request.left)[leftIndex]? = some leftRow ∧
    (nodeEdges request.right)[rightIndex]? = some rightRow ∧
    leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
    Written (width := width) handle ⟨request.domain,leftRow,rightRow⟩ row reader.native.machine.heap ∧
    row.entry.key.symbol = leftRow.entry.key.symbol ∧
    row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
      leftRow.entry.key.constraint rightRow.entry.key.constraint

private theorem rows_writer {before after reader : Checked width} (history : History reader)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (rowSelected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat),
      left[leftIndex]? = some leftRow ∧ right[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      Written (width := width) handle ⟨domain,leftRow,rightRow⟩ row reader.native.machine.heap ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint := by
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
  exact ⟨leftIndex,rightIndex,leftRow,rightRow,handle,leftFound,rightFound,symbols,writer,symbol,guard⟩

/-- One actual captured compiler body forwards to an exact returned request. -/
def Hop (reader : Checked width) (result : Value Symbol Guard)
    (first second : NodeRequest Symbol Guard) : Prop :=
  ∃ (before after : Checked width) (fuel : Nat), Good before ∧
    Trace fuel (.code (compileNode first)) before (.code (.pure result)) after ∧
    Retained after.native reader.native ∧
    ((decision first.domain.key first.left first.right = .swap ∧
        second = ⟨first.domain,first.right,first.left⟩) ∨
     (decision first.domain.key first.left first.right = .reset ∧
        second = ⟨IntersectionEmptyDomain.emptyDomain,first.left,first.right⟩)) ∧
    SourceCurrentNativeForwardLineage.Forwarded reader second before after result

/-- Actual forwarding bodies retain their source order and exact full request. -/
inductive Route (reader : Checked width) (result : Value Symbol Guard) :
    NodeRequest Symbol Guard → NodeRequest Symbol Guard → Prop where
  /-- A request needs no forwarding step. -/
  | refl (request) : Route reader result request request
  /-- One actual body precedes the remaining forwarding bodies. -/
  | step {first middle last} (one : Hop reader result first middle)
      (rest : Route reader result middle last) : Route reader result first last

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem payload_not_forward (left right : Value Symbol Guard) :
    SourceRecursiveIntersectionControl.payload left right ≠ .swap ∧
    SourceRecursiveIntersectionControl.payload left right ≠ .reset := by
  cases left <;> cases right <;> simp [SourceRecursiveIntersectionControl.payload]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem swap_tests (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .swap) :
    reset request.domain.key request.left request.right = false ∧ greater request.left request.right = true := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · rename_i restart
      split at selected
      · cases selected
      · split at selected
        · exact ⟨Bool.eq_false_iff.mpr restart,by assumption⟩
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact False.elim ((payload_not_forward request.left request.right).1 selected)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem reset_test (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .reset) :
    reset request.domain.key request.left request.right = true := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · assumption
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
          · exact False.elim ((payload_not_forward request.left request.right).2 selected)

private def measure (request : NodeRequest Symbol Guard) : Nat :=
  if reset request.domain.key request.left request.right then 2 else if greater request.left request.right then 1 else 0

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem keyable (value : Value Symbol Guard) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free,Value.referenceOf,IntersectionFlatMemoKey.input]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem swap_decreases (request : NodeRequest Symbol Guard)
    (left : request.left.free = []) (right : request.right.free = [])
    (selected : decision request.domain.key request.left request.right = .swap) :
    measure ⟨request.domain,request.right,request.left⟩ < measure request := by
  obtain ⟨restart,ordered⟩ := swap_tests request selected
  obtain ⟨first,firstInput⟩ := keyable request.left left
  obtain ⟨second,secondInput⟩ := keyable request.right right
  have reversed := SourceRecursiveIntersectionSchedule.swap_once request.left request.right first second firstInput secondInput ordered
  have same : reset request.domain.key request.right request.left = false := by
    simpa only [reset,Bool.and_assoc,Bool.and_left_comm] using restart
  simp only [measure,restart,ordered,same,reversed,Bool.false_eq_true,ite_false,ite_true]
  decide

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem reset_decreases (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .reset) :
    measure ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ < measure request := by
  have restart := reset_test request selected
  simp only [measure,restart,ite_true]
  simp only [reset,IntersectionEmptyDomain.emptyDomain,IntersectionEmptyDomain.emptyKey,
    List.isEmpty_nil,Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false]
  split <;> decide

private theorem forwarded_returned {before after reader : Checked width}
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : request.left.free = []) (right : request.right.free = [])
    (forwarded : SourceCurrentNativeForwardLineage.Forwarded reader request before after result) :
    ∃ handle, reader.native.nodes.cells handle = some ⟨request,.returned result⟩ := by
  rcases forwarded.2 with ⟨unresolved,_⟩ | ⟨handle,present,_⟩
  · obtain ⟨first,firstInput⟩ := keyable request.left left
    obtain ⟨second,secondInput⟩ := keyable request.right right
    have key := IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ first second firstInput secondInput
    change IntersectionFlatMemoKeyDomain.sourceKey width request.domain request.left.referenceOf request.right.referenceOf = none at unresolved
    rw [key] at unresolved
    cases unresolved
  · exact ⟨handle,present⟩

private theorem normalize {reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : request.left.free = []) (right : request.right.free = [])
    (returned : ∃ handle,reader.native.nodes.cells handle = some ⟨request,.returned result⟩) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle terminal result reader.native ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .reset := by
  generalize boundEq : measure request = bound
  induction bound using Nat.strongRecOn generalizing request with
  | ind bound ih =>
    obtain ⟨handle,present⟩ := returned
    have writer := SourceCurrentNativeWriterReadyRetention.writers history handle request result present
    by_cases swap : decision request.domain.key request.left request.right = .swap
    · obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,retained⟩ := writer
      have forwarded := SourceCurrentNativeForwardLineage.swap history request fuel result good actual retained swap
      obtain ⟨next,stored⟩ := forwarded_returned _ result right left forwarded
      obtain ⟨terminal,final,route,cell,written,notSwap,notReset⟩ := ih _
        (by rw [← boundEq]; exact swap_decreases request left right swap)
        ⟨request.domain,request.right,request.left⟩ right left ⟨next,stored⟩ rfl
      exact ⟨terminal,final,.step ⟨before,after,fuel,good,actual,retained,.inl ⟨swap,rfl⟩,forwarded⟩ route,
        cell,written,notSwap,notReset⟩
    · by_cases restart : decision request.domain.key request.left request.right = .reset
      · obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,retained⟩ := writer
        have forwarded := SourceCurrentNativeForwardLineage.reset history request fuel result good actual retained restart
        obtain ⟨next,stored⟩ := forwarded_returned
          ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ result left right forwarded
        obtain ⟨terminal,final,route,cell,written,notSwap,notReset⟩ := ih _
          (by rw [← boundEq]; exact reset_decreases request restart)
          ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ left right ⟨next,stored⟩ rfl
        exact ⟨terminal,final,.step ⟨before,after,fuel,good,actual,retained,.inr ⟨restart,rfl⟩,forwarded⟩ route,
          cell,written,notSwap,notReset⟩
      · exact ⟨request,handle,.refl request,present,writer,swap,restart⟩

end MicroCFTA.SourceCurrentNativeQueryRowOrigins
