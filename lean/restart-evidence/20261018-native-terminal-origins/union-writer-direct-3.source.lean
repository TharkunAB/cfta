import MicroCFTA.SourceCurrentNativeWriterReadyRetention
import MicroCFTA.SourceCurrentNativeRowOrigins
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Ordered union member origins at actual captured native writers

A current returned node cell supplies its earlier protected compiler body.
The literal union branch retains the ordered member calls and their exact
full states. Captured operand closedness derives complete original syntax
from the writer input availability. Selected epsilon rows keep their full
guard and ordered children. No internal history or future result law is
assumed.
-/
namespace MicroCFTA.SourceCurrentNativeUnionWriterOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionInputView (Original)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem failed_body {before after : Checked width} (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

/-- The actual captured left-union writer retains a selected row's ordered member call. -/
theorem left {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (returned : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (leftClosed : request.left.free = []) (rightClosed : request.right.free = [])
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftUnion)
    (row : EdgeValue Symbol Guard)
    (origin : MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [result] row) :
    ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      request.left = .union entry members depth free ∧
      ∃ (before after : Checked width) (fuel : Nat),
        Good before ∧ NodeReady before.native.machine request ∧
        before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
        Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
        after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
        Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
          {after with native := finishNode handle result after.native} ∧
        Grows before.native.machine.heap reader.native.machine.heap ∧
        Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
        ∃ (values : List (Value Symbol Guard)) (middle : Checked width) (count : Nat),
          Walk (fun member => requestNode request.domain member request.right) members before values middle count ∧
          ∃ (index : Nat) (member value : Value Symbol Guard) (current next : Checked width)
            (prefixFuel childFuel suffixFuel : Nat),
            members[index]? = some member ∧ values[index]? = some value ∧
            prefixFuel + childFuel + suffixFuel = count ∧
            Walk (fun member => requestNode request.domain member request.right)
              (members.take index) before (values.take index) current prefixFuel ∧
            Trace childFuel (.code (requestNode request.domain member request.right))
              current (.code (.pure value)) next ∧
            Walk (fun member => requestNode request.domain member request.right)
              (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel ∧
            MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [value] row := by
  obtain ⟨before,after,fuel,good,ready,owner,body,ownerKept,finish,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result returned
  have shape : ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      request.left = .union entry members depth free := by
    cases selected : request.left with
    | union entry members depth free => exact ⟨entry,members,depth,free,selected⟩
    | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨entry,members,depth,free,shape⟩ := shape
  have originals := SourceRecursiveIntersectionOriginalOutput.closed_original request.left
    before.native.machine.heap good.heap.semantic.1.normal.facts.coherent ready.2.1 leftClosed
  have otherOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original request.right
    before.native.machine.heap good.heap.semantic.1.normal.facts.coherent ready.2.2 rightClosed
  have memberOriginals : ∀ member ∈ members, Original member := by
    rw [shape] at originals
    cases originals with
    | union _ _ _ _ children => exact children
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
  obtain ⟨values,middle,count,walked,indexed⟩ := SourceCurrentNativeRowOrigins.union request.domain members
    request.right true fuel before after result good.native good.heap
    (fun member found => ⟨memberOriginals member found,otherOriginal⟩) (by simpa using actual)
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,counts,prefixTrace,called,suffixTrace,childOrigin⟩ := indexed _ row origin
  exact ⟨entry,members,depth,free,shape,before,after,fuel,good,ready,owner,body,ownerKept,finish,
    first,last,retained,values,middle,count,by simpa using walked,
    index,member,value,current,next,prefixFuel,childFuel,suffixFuel,memberFound,valueFound,counts,
    by simpa using prefixTrace,
    by simpa using called,
    by simpa using suffixTrace,childOrigin⟩

/-- The actual captured right-union writer retains a selected row's ordered member call. -/
theorem right {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (returned : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (leftClosed : request.left.free = []) (rightClosed : request.right.free = [])
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightUnion)
    (row : EdgeValue Symbol Guard)
    (origin : MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [result] row) :
    ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      request.right = .union entry members depth free ∧
      ∃ (before after : Checked width) (fuel : Nat),
        Good before ∧ NodeReady before.native.machine request ∧
        before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
        Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
        after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
        Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
          {after with native := finishNode handle result after.native} ∧
        Grows before.native.machine.heap reader.native.machine.heap ∧
        Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
        ∃ (values : List (Value Symbol Guard)) (middle : Checked width) (count : Nat),
          Walk (fun member => requestNode request.domain request.left member) members before values middle count ∧
          ∃ (index : Nat) (member value : Value Symbol Guard) (current next : Checked width)
            (prefixFuel childFuel suffixFuel : Nat),
            members[index]? = some member ∧ values[index]? = some value ∧
            prefixFuel + childFuel + suffixFuel = count ∧
            Walk (fun member => requestNode request.domain request.left member)
              (members.take index) before (values.take index) current prefixFuel ∧
            Trace childFuel (.code (requestNode request.domain request.left member))
              current (.code (.pure value)) next ∧
            Walk (fun member => requestNode request.domain request.left member)
              (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel ∧
            MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [value] row := by
  obtain ⟨before,after,fuel,good,ready,owner,body,ownerKept,finish,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result returned
  have shape : ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      request.right = .union entry members depth free := by
    cases selected : request.right with
    | union entry members depth free => exact ⟨entry,members,depth,free,selected⟩
    | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨entry,members,depth,free,shape⟩ := shape
  have originals := SourceRecursiveIntersectionOriginalOutput.closed_original request.right
    before.native.machine.heap good.heap.semantic.1.normal.facts.coherent ready.2.2 rightClosed
  have otherOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original request.left
    before.native.machine.heap good.heap.semantic.1.normal.facts.coherent ready.2.1 leftClosed
  have memberOriginals : ∀ member ∈ members, Original member := by
    rw [shape] at originals
    cases originals with
    | union _ _ _ _ children => exact children
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
  obtain ⟨values,middle,count,walked,indexed⟩ := SourceCurrentNativeRowOrigins.union request.domain members
    request.left false fuel before after result good.native good.heap
    (fun member found => ⟨memberOriginals member found,otherOriginal⟩) (by simpa using actual)
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,counts,prefixTrace,called,suffixTrace,childOrigin⟩ := indexed _ row origin
  exact ⟨entry,members,depth,free,shape,before,after,fuel,good,ready,owner,body,ownerKept,finish,
    first,last,retained,values,middle,count,by simpa using walked,
    index,member,value,current,next,prefixFuel,childFuel,suffixFuel,memberFound,valueFound,counts,
    by simpa using prefixTrace,
    by simpa using called,
    by simpa using suffixTrace,childOrigin⟩

end MicroCFTA.SourceCurrentNativeUnionWriterOrigins
