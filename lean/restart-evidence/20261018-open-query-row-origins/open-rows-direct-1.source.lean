import MicroCFTA.SourceCurrentNativeQueryRowOrigins
import MicroCFTA.SourceCurrentNativeOpenRequestResults

/-!
# Ordinary and union row origins for actual open queries

Actual child requests supply output availability without original syntax
premises. Ordinary rows retain both input indices and their actual writer.
Union origins retain the ordered member call and the same full row.
-/
namespace MicroCFTA.SourceCurrentNativeOpenRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk bind_inverse effects walk_readback)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History Written)
open SourceEqualityNativeDemandMemo (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A joined row keeps both input indices, its actual conjunction and the ordered child pair calls. -/
def Joined (reader : Checked width) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat),
    left[leftIndex]? = some leftRow ∧ right[rightIndex]? = some rightRow ∧
    leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
    Written (width := width) handle ⟨domain,leftRow,rightRow⟩ row reader.native.machine.heap ∧
    row.entry.key.symbol = leftRow.entry.key.symbol ∧
    row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
    ∃ first last count, Good first ∧ Good last ∧
      Grows first.native.machine.heap reader.native.machine.heap ∧
      Grows last.native.machine.heap reader.native.machine.heap ∧
      Walk (fun pair => requestNode domain pair.1 pair.2)
        (leftRow.children.zip rightRow.children) first row.children last count

/-- An actual ordinary compiler return retains both source rows and its full conjunction. -/
theorem ordinary {before after reader : Checked width} (history : History reader)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (rowSelected : (nodeEdges result)[rowIndex]? = some row) :
    Joined reader domain left right row := by
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
  obtain ⟨_before,first,last,count,_good,_ready,_owner,_growth,firstGood,lastGood,firstGrowth,lastGrowth,
    walked,symbol,guard⟩ := SourceCurrentNativeWriterChildOrigins.live writer survives
  exact ⟨leftIndex,rightIndex,leftRow,rightRow,handle,leftFound,rightFound,symbols,writer,symbol,guard,
    first,last,count,firstGood,lastGood,firstGrowth,lastGrowth,walked⟩

private theorem walk_available {A : Type} {inputs : List A}
    (request : A → NodeRequest Symbol Guard) {before after : Checked width}
    {values : List (Value Symbol Guard)} {fuel : Nat}
    (walked : Walk (fun input => requestNode (request input).domain (request input).left (request input).right)
      inputs before values after fuel) (good : Good before) : Values after.native.machine.heap values := by
  induction walked with
  | nil => intro value member; cases member
  | cons input inputs before middle after value values firstFuel restFuel called tail ih =>
      have current := effects called good (by intro value; trivial)
      have available := SourceCurrentNativeOpenRequestResults.node_result firstFuel (request input)
        before middle value good.native called
      have later := ih current.1
      have fields := SourceCurrentAllocatedNativeCodeFields.fields_walk middle.operations
        (fun input => requestNode (request input).domain (request input).left (request input).right)
        inputs (by intro input member value; trivial)
      have final := effects tail.trace current.1 fields
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact final.2.2.1.available value available
      · exact later child member

/-- An actual open union return retains the indexed member call for every complete row origin. -/
theorem union (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (side : Bool) (fuel : Nat) (before after : Checked width) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code ((SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members).bind
      (fun values => .work (makeUnion values) .pure))) before (.code (.pure result)) after) :
    ∃ values middle count,
      Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
        members before values middle count ∧
      ∀ (view : InternedConstructorTemplates.State Symbol Guard) (row : EdgeValue Symbol Guard),
        MergedFreshOrdinaryGraph.Origin view [result] row →
          ∃ index member value current next prefixFuel childFuel suffixFuel,
            members[index]? = some member ∧ values[index]? = some value ∧
            prefixFuel + childFuel + suffixFuel = count ∧
            Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
              (members.take index) before (values.take index) current prefixFuel ∧
            Trace childFuel (.code (if side then requestNode domain member other else requestNode domain other member))
              current (.code (.pure value)) next ∧
            Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
              (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel ∧
            MergedFreshOrdinaryGraph.Origin view [value] row := by
  obtain ⟨inner,outer,values,middle,count,first,last⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members))
    (fun values => .work (makeUnion values) .pure) before after result actual
  have fields := SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations
    (fun member => if side then requestNode domain member other else requestNode domain other member)
    members (by intro member present value; cases side <;> trivial)
  have current := effects first good fields
  have walked := walk_readback _ _ inner _ _ _ first
  have available : Values middle.native.machine.heap values := by
    let request := fun member => if side then (⟨domain,member,other⟩ : NodeRequest Symbol Guard) else ⟨domain,other,member⟩
    have same : (fun member => if side then requestNode domain member other else requestNode domain other member) =
        (fun member => requestNode (request member).domain (request member).left (request member).right) := by
      funext member; cases side <;> rfl
    rw [same] at walked
    exact walk_available request walked good
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  refine ⟨values,middle,inner,walked,?_⟩
  intro view row origin
  have included := (MergedFreshOrdinaryUnionOrigins.union_origins middle.native.machine.heap view
    current.1.heap.semantic.1.normal.facts current.1.heap.semantic.1.normal.live values available row).mp
    (by simpa only [observed.1] using origin)
  obtain ⟨value,member,origin⟩ := included
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨request,current,next,prefixFuel,childFuel,suffixFuel,input,counts,prefix,child,suffix⟩ :=
    SourceCurrentNativeRowOrigins.indexed walked index value found
  exact ⟨index,request,value,current,next,prefixFuel,childFuel,suffixFuel,input,found,counts,prefix,child,suffix,origin⟩

end MicroCFTA.SourceCurrentNativeOpenRowOrigins

