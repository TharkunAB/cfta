import MicroCFTA.SourceCurrentNativeActivePairedRows
import MicroCFTA.SourceCurrentNativeActiveUnionRowOrigins
import MicroCFTA.SourceCurrentNativeActiveReferenceOrigins
import MicroCFTA.SourceCurrentNativeActiveMuBodyOrigins

/-!
# Exhaustive active terminal row producers

One normalized returned writer supplies every supported row branch.
Ordinary rows retain their paired source rows, including nullary rows.
Union and reference rows retain their actual child calls at the same reader.
-/
namespace MicroCFTA.SourceCurrentNativeActiveRowProduction
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
open SourceCurrentNativeMuBodyOrigins (Body)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionControl (decision)
open SourceCurrentNativeQueryRowOrigins (Route)
open SourceCurrentNativeForwardLineage (Forwarded)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The selected Mu writer retains its actual entered body and optional construction. -/
def Mu (reader : Checked width) (request : NodeRequest Symbol Guard)
    (result : Node) (handle : Nat) : Prop :=
    ∃ before after fuel, Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      Body reader fuel request before result after ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
        {after with native := finishNode handle result after.native} ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native

/-- The selected union writer retains its indexed member call for the same complete row. -/
def Union (reader : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Node) (side : Bool) (row : EdgeValue Symbol Guard) : Prop :=
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
            SourceCurrentNativeActiveUnionRowOrigins.Call reader (if side then ⟨request.domain,member,request.right⟩ else ⟨request.domain,request.left,member⟩)
              current next childFuel value row ∧
            Walk (fun member => if side then requestNode request.domain member request.right
              else requestNode request.domain request.left member)
              (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel

/-- The selected reference writer retains its exact read and ordered resolved child call. -/
def Reference (reader : Checked width) (request : NodeRequest Symbol Guard)
    (side : Bool) (result : Node) (handle : Nat) : Prop :=
    ∃ before after fuel, Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      (∃ (name : Nat) (bound : Value Symbol Guard) (childFuel : Nat),
        (if side then request.left else request.right) = .reference (.interned name) ∧
        fuel = childFuel + 1 ∧ childFuel < fuel ∧
        name ∈ SourceRecursiveIntersectionDomain.names request.domain.key ∧
        SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
        Trace childFuel (.code (if side then requestNode request.domain bound request.right
          else requestNode request.domain request.left bound)) before (.code (.pure result)) after ∧
        Good after ∧
        Forwarded reader (if side then ⟨request.domain,bound,request.right⟩
          else ⟨request.domain,request.left,bound⟩) before after result) ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
        {after with native := finishNode handle result after.native} ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native

/-- Every selected terminal row has one explicit actual source branch. -/
def Cases (reader : Checked width) (request : NodeRequest Symbol Guard)
    (result : Node) (handle rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  (decision request.domain.key request.left request.right = .self ∧
    (nodeEdges request.left)[rowIndex]? = some row) ∨
  (decision request.domain.key request.left request.right = .ordinary ∧
    SourceCurrentNativeActivePairedRows.Joined reader request row) ∨
  ((decision request.domain.key request.left request.right = .bothMu ∨
    decision request.domain.key request.left request.right = .leftMu ∨
    decision request.domain.key request.left request.right = .rightMu) ∧ Mu reader request result handle) ∨
  (decision request.domain.key request.left request.right = .leftUnion ∧ Union reader handle request result true row) ∨
  (decision request.domain.key request.left request.right = .rightUnion ∧ Union reader handle request result false row) ∨
  (decision request.domain.key request.left request.right = .leftReference ∧ Reference reader request true result handle) ∨
  (decision request.domain.key request.left request.right = .rightReference ∧ Reference reader request false result handle)

private theorem failed_body {before after : Checked width} (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure) (result : Node)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

/-- The supplied terminal writer derives a source branch without internal History or a branch premise. -/
theorem terminal {reader : Checked width}
    (nodes : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Node),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (edges : ∀ (handle : Nat) (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard),
      reader.native.edges.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeEdgeWriterRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (result : Node) (handle : Nat)
    (written : SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (notSwap : decision request.domain.key request.left request.right ≠ .swap)
    (notReset : decision request.domain.key request.left request.right ≠ .reset)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Cases reader request result handle rowIndex row := by
  have chosen := written
  obtain ⟨before,after,fuel,good,ready,owner,actual,kept,finish,first,last,retained⟩ := written
  have rowOrigin : MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [result] row :=
    ⟨result,.seed (by simp),List.mem_of_getElem? selected⟩
  unfold Cases
  cases branch : decision request.domain.key request.left request.right with
  | self =>
    have same := SourceCurrentNativeForwardLineage.self request fuel result actual branch
    exact .inl ⟨rfl,by simpa only [same.2.1] using selected⟩
  | ordinary =>
    obtain ⟨start,stop,count,checked,input,started,body,ended,finished,initialGrowth,finalGrowth,saved,joined⟩ :=
      SourceCurrentNativeActivePairedRows.returned edges handle request result chosen branch rowIndex row selected
    exact .inr (.inl ⟨rfl,joined⟩)
  | bothMu | leftMu | rightMu =>
    have muBranch : decision request.domain.key request.left request.right = .bothMu ∨
        decision request.domain.key request.left request.right = .leftMu ∨
        decision request.domain.key request.left request.right = .rightMu := by simp [branch]
    exact .inr (.inr (.inl ⟨by simp,SourceCurrentNativeActiveMuBodyOrigins.returned nodes request result handle chosen muBranch⟩))
  | leftUnion =>
    exact .inr (.inr (.inr (.inl ⟨rfl,SourceCurrentNativeActiveUnionRowOrigins.returned nodes handle request result chosen true branch row rowOrigin⟩)))
  | rightUnion =>
    exact .inr (.inr (.inr (.inr (.inl ⟨rfl,SourceCurrentNativeActiveUnionRowOrigins.returned nodes handle request result chosen false branch row rowOrigin⟩))))
  | leftReference =>
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl,SourceCurrentNativeActiveReferenceOrigins.returned nodes request true result handle chosen branch⟩)))))
  | rightReference =>
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨rfl,SourceCurrentNativeActiveReferenceOrigins.returned nodes request false result handle chosen branch⟩)))))
  | swap => exact False.elim (notSwap branch)
  | reset => exact False.elim (notReset branch)
  | empty =>
    have compiled : compileNode request = .pure .empty := by unfold compileNode; simp only [branch]
    rw [compiled] at actual
    have same := pure_trace fuel Value.empty result before after actual.steps
    rw [←same.2.1] at selected
    simp only [nodeEdges,List.getElem?_nil] at selected
    cases selected
  | repeated key =>
    have compiled : compileNode request = .pure (.reference (.intersection key.1 key.2)) := by
      unfold compileNode
      simp only [branch,SourceRecursiveIntersectionControl.repeatedValue]
    rw [compiled] at actual
    have same := pure_trace fuel (.reference (.intersection key.1 key.2)) result before after actual.steps
    rw [←same.2.1] at selected
    simp only [nodeEdges,List.getElem?_nil] at selected
    cases selected
  | unsupported =>
    have compiled : compileNode request = .fail (.unsupported request.left.referenceOf request.right.referenceOf) := by
      unfold compileNode
      simp only [branch,SourceRecursiveIntersectionCode.unsupported]
    exact (failed_body fuel _ result (compiled ▸ actual)).elim

/-- One actual forwarded result derives its same normalized writer and an exhaustive row producer. -/
theorem forwarded {reader before after : Checked width}
    (nodes : ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (result : Node),
      reader.native.nodes.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native)
    (edges : ∀ (handle : Nat) (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard),
      reader.native.edges.cells handle = some ⟨request,.returned result⟩ →
        SourceCurrentNativeEdgeWriterRetention.Written handle request result reader.native)
    (request : NodeRequest Symbol Guard) (result : Node)
    (actual : Forwarded reader request before after result)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written handle terminal result reader.native ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
      (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
      Cases reader terminal result handle rowIndex row := by
  have nonempty : result ≠ .empty := by
    intro same
    rw [same] at selected
    simp only [nodeEdges,List.getElem?_nil] at selected
    cases selected
  obtain ⟨terminal,handle,route,cell,writer,notSwap,notReset,left,right⟩ :=
    SourceCurrentNativeActiveQueryForwarding.normalize nodes request result actual nonempty
  exact ⟨terminal,handle,route,cell,writer,notSwap,notReset,left,right,
    SourceCurrentNativeActiveRowProduction.terminal nodes edges terminal result handle writer notSwap notReset rowIndex row selected⟩

/-- An actual clean prefix supplies the writer maps for the same forwarded row production. -/
theorem «prefix» {A : Type} (control final : Control A) (initial reader : Checked width) (count : Nat)
    (clean : SourceEqualityNativeDemandBodyCode.Clean control) (good : Good initial)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control initial)
    (history : SourceCurrentNativeEdgeWriterGrowth.History initial)
    (actual : Trace count control initial final reader)
    (request : NodeRequest Symbol Guard) (result : Node) (before after : Checked width)
    (called : Forwarded reader request before after result)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written handle terminal result reader.native ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
      (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
      Cases reader terminal result handle rowIndex row := by
  have maps := SourceCurrentNativePrefixWriterMaps.prefix control initial reader final count clean good fields history actual
  exact forwarded maps.1 maps.2.1 request result called rowIndex row selected

end MicroCFTA.SourceCurrentNativeActiveRowProduction
