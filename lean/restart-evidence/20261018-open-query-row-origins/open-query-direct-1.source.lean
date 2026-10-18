import MicroCFTA.SourceCurrentNativeOpenRowOrigins
import MicroCFTA.SourceCurrentNativeOpenQueryForwarding
import MicroCFTA.SourceCurrentNativeMuWriterSourceRows
import MicroCFTA.SourceCurrentNativeReferenceOrigins
import MicroCFTA.SourceCurrentNativeRowKeyable

/-!
# Actual row origins of native open queries

Selected physical rows derive input codecs from the actual query trace.
Actual forwarding reaches self, ordinary, Mu, union, or reference writers.
Each branch retains its actual calls at the final reader.
Generated body anchors do not assert initial operand source ancestry.
-/
namespace MicroCFTA.SourceCurrentNativeOpenQueryRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeQueryRowOrigins (Route)
open SourceCurrentNativeQueryTerminalOrigins (Union)
open SourceCurrentNativeMuWriterSourceRows (MuRow)
open SourceCurrentNativeForwardLineage (Forwarded)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionControl (decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
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

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem failed_body {before after : Checked width} (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

/-- A reference origin retains the captured read and the exact resolved child's reader provenance. -/
def Reference (side : Bool) (reader : Checked width) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) : Prop :=
  ∃ (before after : Checked width) (fuel : Nat),
    Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
      {after with native := finishNode handle result after.native} ∧
    Grows before.native.machine.heap reader.native.machine.heap ∧
    Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
    ∃ (name : Nat) (bound : Value Symbol Guard) (childFuel : Nat),
      (if side then request.left else request.right) = .reference (.interned name) ∧
      fuel = childFuel + 1 ∧ name ∈ SourceRecursiveIntersectionDomain.names request.domain.key ∧
      SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
      Trace childFuel (.code (if side then requestNode request.domain bound request.right
        else requestNode request.domain request.left bound)) before (.code (.pure result)) after ∧
      Forwarded reader (if side then ⟨request.domain,bound,request.right⟩
        else ⟨request.domain,request.left,bound⟩) before after result

/-- Every selected physical row retains its actual terminal writer and supported branch origin. -/
def Resolved (reader : Checked width) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ terminal handle, Route reader result request terminal ∧
    (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
    (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
    reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
    SourceCurrentNativeWriterReadyRetention.Written (width := width) handle terminal result reader.native ∧
    ((decision terminal.domain.key terminal.left terminal.right = .self ∧
        (nodeEdges terminal.left)[rowIndex]? = some row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .ordinary ∧
        SourceCurrentNativeOpenRowOrigins.Joined reader terminal.domain
          (nodeEdges terminal.left) (nodeEdges terminal.right) row) ∨
     ((decision terminal.domain.key terminal.left terminal.right = .bothMu ∨
       decision terminal.domain.key terminal.left terminal.right = .leftMu ∨
       decision terminal.domain.key terminal.left terminal.right = .rightMu) ∧ MuRow reader handle terminal result rowIndex row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .leftUnion ∧ Union true reader handle terminal result row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .rightUnion ∧ Union false reader handle terminal result row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .leftReference ∧ Reference true reader handle terminal result) ∨
     (decision terminal.domain.key terminal.left terminal.right = .rightReference ∧ Reference false reader handle terminal result))

private theorem union_left {reader : Checked width} (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (written : SourceCurrentNativeWriterReadyRetention.Written (width := width) handle request result reader.native)
    (branch : decision request.domain.key request.left request.right = .leftUnion)
    (row : EdgeValue Symbol Guard)
    (origin : MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [result] row) :
    Union true reader handle request result row := by
  obtain ⟨before,after,fuel,good,ready,owner,body,ownerKept,finish,first,last,retained⟩ :=
    written
  have shape : ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      request.left = .union entry members depth free := by
    cases selected : request.left with
    | union entry members depth free => exact ⟨entry,members,depth,free,rfl⟩
    | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨entry,members,depth,free,shape⟩ := shape
  have compiled : compileNode request =
      (SourceRecursiveIntersectionCode.walk (fun member => requestNode request.domain member request.right) members).bind
        (fun values => .work (makeUnion values) .pure) := by
    unfold compileNode
    dsimp only
    rw [branch,shape]
  have actual : Trace fuel (.code ((SourceRecursiveIntersectionCode.walk (fun member => requestNode request.domain member request.right) members).bind
      (fun values => .work (makeUnion values) .pure))) before (.code (.pure result)) after := by
    rw [← compiled]
    exact body
  obtain ⟨values,middle,count,walked,indexed⟩ := SourceCurrentNativeOpenRowOrigins.union request.domain members
    request.right true fuel before after result good (by simpa using actual)
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,counts,prefixTrace,called,suffixTrace,childOrigin⟩ := indexed _ row origin
  exact ⟨entry,members,depth,free,shape,before,after,fuel,good,ready,owner,body,ownerKept,finish,
    first,last,retained,values,middle,count,by simpa using walked,
    index,member,value,current,next,prefixFuel,childFuel,suffixFuel,memberFound,valueFound,counts,
    by simpa using prefixTrace,
    by simpa using called,
    by simpa using suffixTrace,childOrigin⟩


private theorem union_right {reader : Checked width} (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (written : SourceCurrentNativeWriterReadyRetention.Written (width := width) handle request result reader.native)
    (branch : decision request.domain.key request.left request.right = .rightUnion)
    (row : EdgeValue Symbol Guard)
    (origin : MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [result] row) :
    Union false reader handle request result row := by
  obtain ⟨before,after,fuel,good,ready,owner,body,ownerKept,finish,first,last,retained⟩ :=
    written
  have shape : ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      request.right = .union entry members depth free := by
    cases selected : request.right with
    | union entry members depth free => exact ⟨entry,members,depth,free,rfl⟩
    | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨entry,members,depth,free,shape⟩ := shape
  have compiled : compileNode request =
      (SourceRecursiveIntersectionCode.walk (fun member => requestNode request.domain request.left member) members).bind
        (fun values => .work (makeUnion values) .pure) := by
    unfold compileNode
    dsimp only
    rw [branch,shape]
  have actual : Trace fuel (.code ((SourceRecursiveIntersectionCode.walk (fun member => requestNode request.domain request.left member) members).bind
      (fun values => .work (makeUnion values) .pure))) before (.code (.pure result)) after := by
    rw [← compiled]
    exact body
  obtain ⟨values,middle,count,walked,indexed⟩ := SourceCurrentNativeOpenRowOrigins.union request.domain members
    request.left false fuel before after result good (by simpa using actual)
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,counts,prefixTrace,called,suffixTrace,childOrigin⟩ := indexed _ row origin
  exact ⟨entry,members,depth,free,shape,before,after,fuel,good,ready,owner,body,ownerKept,finish,
    first,last,retained,values,middle,count,by simpa using walked,
    index,member,value,current,next,prefixFuel,childFuel,suffixFuel,memberFound,valueFound,counts,
    by simpa using prefixTrace,
    by simpa using called,
    by simpa using suffixTrace,childOrigin⟩


/-- A returned keyable query derives every terminal branch without closed or original syntax premises. -/
theorem returned {reader : Checked width} (history : History reader)
    (publications : SourceCurrentNativeMuPublication.History empty reader.native.machine.heap)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (handle : Nat) (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Resolved reader request result rowIndex row := by
  obtain ⟨terminal,owner,route,cell,writer,notSwap,notReset,firstCodec,secondCodec⟩ :=
    SourceCurrentNativeOpenQueryForwarding.normalize history request result left right ⟨handle,present⟩
  refine ⟨terminal,owner,route,firstCodec,secondCodec,cell,writer,?_⟩
  obtain ⟨before,after,fuel,good,ready,started,body,ownerKept,finish,firstGrowth,lastGrowth,retained⟩ := writer
  have rowOrigin : MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [result] row :=
    ⟨result,.seed (by simp),List.mem_of_getElem? selected⟩
  cases branch : decision terminal.domain.key terminal.left terminal.right with
  | self =>
      have same := SourceCurrentNativeForwardLineage.self terminal fuel result body branch
      exact .inl ⟨rfl,by simpa only [same.2.1] using selected⟩
  | ordinary =>
      rw [ordinary_code terminal branch] at body
      have joined := SourceCurrentNativeOpenRowOrigins.ordinary history terminal.domain
        (nodeEdges terminal.left) (nodeEdges terminal.right) fuel result good body retained rowIndex row selected
      exact .inr (.inl ⟨rfl,joined⟩)
  | bothMu | leftMu | rightMu =>
      have selectedMu : decision terminal.domain.key terminal.left terminal.right = .bothMu ∨
          decision terminal.domain.key terminal.left terminal.right = .leftMu ∨
          decision terminal.domain.key terminal.left terminal.right = .rightMu := by simp [branch]
      exact .inr (.inr (.inl ⟨selectedMu,SourceCurrentNativeMuWriterSourceRows.returned_mu
        history publications terminal result owner cell selectedMu rowIndex row selected⟩))
  | leftUnion =>
      exact .inr (.inr (.inr (.inl ⟨rfl,union_left owner terminal result writer branch row rowOrigin⟩)))
  | rightUnion =>
      exact .inr (.inr (.inr (.inr (.inl ⟨rfl,union_right owner terminal result writer branch row rowOrigin⟩))))
  | leftReference =>
      obtain ⟨name,bound,count,shape,total,member,found,called⟩ :=
        SourceCurrentNativeReferenceOrigins.left terminal fuel result body branch
      have forwarded := SourceCurrentNativeReferenceOrigins.forwarded history _ count result good called retained
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl,
        before,after,fuel,good,ready,started,body,ownerKept,finish,firstGrowth,lastGrowth,retained,
        name,bound,count,shape,total,member,found,called,forwarded⟩)))))
  | rightReference =>
      obtain ⟨name,bound,count,shape,total,member,found,called⟩ :=
        SourceCurrentNativeReferenceOrigins.right terminal fuel result body branch
      have forwarded := SourceCurrentNativeReferenceOrigins.forwarded history _ count result good called retained
      exact .inr (.inr (.inr (.inr (.inr (.inr ⟨rfl,
        before,after,fuel,good,ready,started,body,ownerKept,finish,firstGrowth,lastGrowth,retained,
        name,bound,count,shape,total,member,found,called,forwarded⟩)))))
  | swap => exact False.elim (notSwap branch)
  | reset => exact False.elim (notReset branch)
  | empty =>
      have compiled : compileNode terminal = .pure .empty := by unfold compileNode; simp only [branch]
      rw [compiled] at body
      have same := pure_trace fuel Value.empty result before after body.steps
      rw [← same.2.1] at selected
      simp only [nodeEdges,List.getElem?_nil] at selected
      cases selected
  | repeated key =>
      have compiled : compileNode terminal = .pure (.reference (.intersection key.1 key.2)) := by
        unfold compileNode
        simp only [branch,SourceRecursiveIntersectionControl.repeatedValue]
      rw [compiled] at body
      have same := pure_trace fuel (.reference (.intersection key.1 key.2)) result before after body.steps
      rw [← same.2.1] at selected
      simp only [nodeEdges,List.getElem?_nil] at selected
      cases selected
  | unsupported =>
      have compiled : compileNode terminal = .fail (.unsupported terminal.left.referenceOf terminal.right.referenceOf) := by
        unfold compileNode
        simp only [branch,SourceRecursiveIntersectionCode.unsupported]
      rw [compiled] at body
      exact False.elim (failed_body fuel _ result body)

/-- Initial causal histories and an actual selected row derive open query terminal origins and their reader. -/
theorem request {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before) (history : History before)
    (publications : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) ∧
      Resolved after input result rowIndex row := by
  obtain ⟨first,second,key,left,right,keyed⟩ := SourceCurrentNativeRowKeyable.selected input fuel result actual rowIndex row selected
  obtain ⟨_,⟨published⟩⟩ := SourceCurrentNativePublicationTrace.from_history actual good.heap.semantic publications
  obtain ⟨reached,checked,growth,origin⟩ := SourceCurrentSharedLeafNativeLineage.request input fuel result good history actual
  have returnedCell : ∃ handle, after.native.nodes.cells handle = some ⟨input,.returned result⟩ := by
    rcases origin with ⟨missing,_⟩ | ⟨handle,present,_⟩
    · rw [keyed] at missing
      cases missing
    · exact ⟨handle,present⟩
  obtain ⟨handle,present⟩ := returnedCell
  exact ⟨reached,checked,growth,⟨published⟩,returned reached published input result ⟨first,left⟩ ⟨second,right⟩
    handle present rowIndex row selected⟩

end MicroCFTA.SourceCurrentNativeOpenQueryRowOrigins
