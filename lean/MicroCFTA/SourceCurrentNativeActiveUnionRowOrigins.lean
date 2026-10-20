import MicroCFTA.SourceCurrentNativeActiveQueryForwarding
import MicroCFTA.SourceCurrentNativeOriginExposure
import MicroCFTA.SourceCurrentNativeOpenRowOrigins
import MicroCFTA.InternedValueMass

/-!
# Actual active union row producers

Each selected union row retains the chosen historical compiler writer.
Its actual ordered member call keeps a returned child writer at the same
reader. No completed History at the active reader is required.
-/
namespace MicroCFTA.SourceCurrentNativeActiveUnionRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityNativeDemandMemo (Retained)
open MergedFreshOrdinaryGraph (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A complete child origin derives its keyed returned cell at the same reader. -/
def Call (reader : Checked width) (request : NodeRequest Symbol Guard)
    (before after : Checked width) (fuel : Nat) (value : Value Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  Good before ∧ Good after ∧ NodeReady before.native.machine request ∧
  Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after ∧
  Grows before.native.machine.heap reader.native.machine.heap ∧
  Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
  Origin reader.native.machine.heap [value] row ∧
  ∃ first second key handle,
    IntersectionFlatMemoKey.input request.left.referenceOf = some first ∧
    IntersectionFlatMemoKey.input request.right.referenceOf = some second ∧
    SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key ∧
    reader.native.nodes.cells handle = some ⟨request,.returned value⟩ ∧
    SourceCurrentNativeWriterReadyRetention.Written (width := width) handle request value reader.native

private theorem call {reader before after : Checked width} (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (value : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after)
    (first : Grows before.native.machine.heap reader.native.machine.heap)
    (last : Grows after.native.machine.heap reader.native.machine.heap)
    (retained : Retained after.native reader.native)
    (row : EdgeValue Symbol Guard) (origin : Origin reader.native.machine.heap [value] row) :
    Call reader request before after fuel value row := by
  obtain ⟨left,right,key,leftCodec,rightCodec,keyed⟩ :=
    SourceCurrentNativeOriginExposure.keyable request fuel value actual _ row origin
  obtain ⟨_,direct | ⟨handle,cell,writer⟩⟩ :=
    SourceCurrentNativeActiveQueryForwarding.forwarded writers request fuel value good actual retained
  · rw [keyed] at direct
    cases direct.1
  · exact ⟨good,(effects actual good (by intro value; trivial)).1,
      (SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs actual).1,
      actual,first,last,retained,origin,left,right,key,handle,leftCodec,rightCodec,keyed,cell,writer⟩

private theorem failed_body {before after : Checked width} (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

private theorem union_call {reader before after : Checked width} (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (side : Bool)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code ((SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members).bind
      (fun values => .work (makeUnion values) .pure))) before (.code (.pure result)) after)
    (growth : Grows after.native.machine.heap reader.native.machine.heap)
    (retained : Retained after.native reader.native)
    (row : EdgeValue Symbol Guard) (origin : Origin reader.native.machine.heap [result] row) :
    ∃ values middle count,
      Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
        members before values middle count ∧
      ∃ index member value current next prefixFuel childFuel suffixFuel,
        members[index]? = some member ∧ values[index]? = some value ∧
        prefixFuel + childFuel + suffixFuel = count ∧
        Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
          (members.take index) before (values.take index) current prefixFuel ∧
        Call reader (if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩)
          current next childFuel value row ∧
        Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
          (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel := by
  obtain ⟨values,middle,count,walked,indexed⟩ := SourceCurrentNativeOpenRowOrigins.union
    domain members other side fuel before after result good actual
  obtain ⟨inner,outer,rawValues,rawMiddle,_,first,made⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members))
    (fun values => .work (makeUnion values) .pure) before after result actual
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
    (fun member => if side then requestNode domain member other else requestNode domain other member)
    members (by intro member included; cases side <;> intro value <;> trivial)
  have middleFacts := effects walked.trace good walkFields
  have finalFacts := effects made middleFacts.1
    ⟨SourceCurrentAllocatedNativeCodeFields.makeUnion_fields middle.operations values,by intro value; trivial⟩
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,total,prefixTrace,called,suffix,childOrigin⟩ := indexed _ row origin
  have prefixFields := SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations
    (fun member => if side then requestNode domain member other else requestNode domain other member)
    (members.take index) (by intro member included; cases side <;> intro value <;> trivial)
  have currentFacts := effects prefixTrace.trace good prefixFields
  have actualChild : Trace childFuel (.code (requestNode
      ((if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩) : NodeRequest Symbol Guard).domain
      ((if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩) : NodeRequest Symbol Guard).left
      ((if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩) : NodeRequest Symbol Guard).right))
      current (.code (.pure value)) next := by cases side <;> exact called
  have nextFacts := effects actualChild currentFacts.1 (by intro value; trivial)
  have suffixFields := SourceCurrentAllocatedNativeCodeFields.fields_walk next.operations
    (fun member => if side then requestNode domain member other else requestNode domain other member)
    (members.drop (index + 1)) (by intro member included; cases side <;> intro value <;> trivial)
  have suffixFacts := effects suffix.trace nextFacts.1 suffixFields
  have suffixRetained := SourceCurrentNativeWriterReadyRetention.trace_retained suffix.trace nextFacts.1.native.shape
  have finalRetained := SourceCurrentNativeWriterReadyRetention.trace_retained made middleFacts.1.native.shape
  have last := grows_trans suffixFacts.2.2.1.growth (grows_trans finalFacts.2.2.1.growth growth)
  exact ⟨values,middle,count,walked,index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,total,prefixTrace,
    call writers _ childFuel value currentFacts.1 actualChild
      (grows_trans nextFacts.2.2.1.growth last) last
      (suffixRetained.trans (finalRetained.trans retained)) row childOrigin,suffix⟩

/-- An actual union writer retains the indexed smaller member and its keyed child origin. -/
theorem returned {reader : Checked width} (writers : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (written : SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (side : Bool)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right =
      if side then .leftUnion else .rightUnion)
    (row : EdgeValue Symbol Guard) (origin : Origin reader.native.machine.heap [result] row) :
    ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      (if side then request.left else request.right) = .union entry members depth free ∧
      ∃ (before after : Checked width) (fuel : Nat),
        Good before ∧ NodeReady before.native.machine request ∧
        before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
        Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
        after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
        Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
          {after with native := finishNode handle result after.native} ∧
        Grows before.native.machine.heap reader.native.machine.heap ∧
        Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
        ∃ values middle count,
          Walk (fun member => if side then requestNode request.domain member request.right
            else requestNode request.domain request.left member) members before values middle count ∧
          ∃ index member value current next prefixFuel childFuel suffixFuel,
            members[index]? = some member ∧ values[index]? = some value ∧
            InternedValueMass.value member < InternedValueMass.value (if side then request.left else request.right) ∧
            prefixFuel + childFuel + suffixFuel = count ∧
            Walk (fun member => if side then requestNode request.domain member request.right
              else requestNode request.domain request.left member)
              (members.take index) before (values.take index) current prefixFuel ∧
            Call reader (if side then ⟨request.domain,member,request.right⟩ else ⟨request.domain,request.left,member⟩)
              current next childFuel value row ∧
            Walk (fun member => if side then requestNode request.domain member request.right
              else requestNode request.domain request.left member)
              (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel := by
  obtain ⟨before,after,fuel,good,ready,owner,body,kept,finish,first,last,retained⟩ :=
    written
  have shape : ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      (if side then request.left else request.right) = .union entry members depth free := by
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at branch ⊢
    · cases selected : request.right with
      | union entry members depth free => exact ⟨entry,members,depth,free,rfl⟩
      | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
    · cases selected : request.left with
      | union entry members depth free => exact ⟨entry,members,depth,free,rfl⟩
      | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨entry,members,depth,free,shape⟩ := shape
  have compiled : compileNode request =
      (SourceRecursiveIntersectionCode.walk (fun member => if side then requestNode request.domain member request.right
        else requestNode request.domain request.left member) members).bind
        (fun values => .work (makeUnion values) .pure) := by
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at branch shape ⊢ <;>
      unfold compileNode <;> dsimp only <;> rw [branch,shape]
  have actual := compiled ▸ body
  obtain ⟨values,middle,count,walked,index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,total,prefixTrace,child,suffix⟩ := union_call writers request.domain members
      (if side then request.right else request.left) side fuel result good (by cases side <;> exact actual)
      last retained row origin
  have small := InternedValueMass.union_member_lt entry members depth free member (List.mem_of_getElem? memberFound)
  rw [← shape] at small
  refine ⟨entry,members,depth,free,shape,before,after,fuel,good,ready,owner,body,kept,finish,first,last,retained,
    values,middle,count,?_,index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,small,total,?_,?_,?_⟩ <;> cases side <;> assumption

end MicroCFTA.SourceCurrentNativeActiveUnionRowOrigins
