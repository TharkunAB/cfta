import MicroCFTA.SourceCurrentNativeQueryClosedTerminal
import MicroCFTA.SourceCurrentNativeUnionWriterOrigins
import MicroCFTA.SourceCurrentNativeMuWriterOrigins

/-!
# Actual closed query rows at their captured terminal writers

Closed root forwarding excludes reference terminal branches. Union rows
retain their actual ordered member calls. Mu branches retain their actual
entered body and binder schedule. Used-Mu row alignment remains separate.
-/
namespace MicroCFTA.SourceCurrentNativeQueryTerminalOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeQueryRowOrigins (Route Joined)
open SourceRecursiveIntersectionControl (decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A Mu origin retains its actual captured compiler body and exact internal schedule. -/
def Mu (reader : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Value Symbol Guard) : Prop :=
  ∃ before after fuel, Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    SourceCurrentNativeMuWriterOrigins.Schedule fuel request before result after ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Grows before.native.machine.heap reader.native.machine.heap ∧
    Grows after.native.machine.heap reader.native.machine.heap ∧
    SourceEqualityNativeDemandMemo.Retained after.native reader.native

/-- A union origin retains the full captured writer and selected ordered member call. -/
def Union (side : Bool) (reader : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Value Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
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
      Grows after.native.machine.heap reader.native.machine.heap ∧
      SourceEqualityNativeDemandMemo.Retained after.native reader.native ∧
      ∃ (values : List (Value Symbol Guard)) (middle : Checked width) (count : Nat),
        let call := fun member => if side then requestNode request.domain member request.right
          else requestNode request.domain request.left member
        Walk call members before values middle count ∧
        ∃ (index : Nat) (member value : Value Symbol Guard) (current next : Checked width)
            (prefixFuel childFuel suffixFuel : Nat),
          members[index]? = some member ∧ values[index]? = some value ∧
          prefixFuel + childFuel + suffixFuel = count ∧
          Walk call (members.take index) before (values.take index) current prefixFuel ∧
          Trace childFuel (.code (call member)) current (.code (.pure value)) next ∧
          Walk call (members.drop (index+1)) next (values.drop (index+1)) middle suffixFuel ∧
          MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [value] row

/-- Every closed selected row has an exact terminal writer and an explicit supported branch origin. -/
def Resolved (reader : Checked width) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ terminal handle, Route reader result request terminal ∧
    terminal.left.free = [] ∧ terminal.right.free = [] ∧
    reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
    SourceCurrentNativeWriterReadyRetention.Written (width := width) handle terminal result reader.native ∧
    ((decision terminal.domain.key terminal.left terminal.right = .self ∧
        (nodeEdges terminal.left)[rowIndex]? = some row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .ordinary ∧ Joined reader terminal row) ∨
     ((decision terminal.domain.key terminal.left terminal.right = .bothMu ∨
       decision terminal.domain.key terminal.left terminal.right = .leftMu ∨
       decision terminal.domain.key terminal.left terminal.right = .rightMu) ∧ Mu reader handle terminal result) ∨
     (decision terminal.domain.key terminal.left terminal.right = .leftUnion ∧ Union true reader handle terminal result row) ∨
     (decision terminal.domain.key terminal.left terminal.right = .rightUnion ∧ Union false reader handle terminal result row))

/-- An actual returned query derives its captured terminal origin without a residual branch assumption. -/
theorem returned {reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : request.left.free = []) (right : request.right.free = [])
    (handle : Nat) (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    Resolved reader request result rowIndex row := by
  have origin := SourceCurrentNativeQueryRowOrigins.returned history request result left right handle present rowIndex row selected
  obtain ⟨terminal,owner,route,closedLeft,closedRight,cell,writer,cases⟩ :=
    SourceCurrentNativeQueryClosedTerminal.closed_residual origin left right
  have rowOrigin : MergedFreshOrdinaryGraph.Origin reader.native.machine.heap [result] row :=
    ⟨result,.seed (by simp),List.mem_of_getElem? selected⟩
  refine ⟨terminal,owner,route,closedLeft,closedRight,cell,writer,?_⟩
  rcases cases with self | ordinary | both | first | second | leftUnion | rightUnion
  · exact .inl self
  · exact .inr (.inl ordinary)
  · exact .inr (.inr (.inl ⟨.inl both,
      SourceCurrentNativeMuWriterOrigins.returned history terminal result owner cell (.inl both)⟩))
  · exact .inr (.inr (.inl ⟨.inr (.inl first),
      SourceCurrentNativeMuWriterOrigins.returned history terminal result owner cell (.inr (.inl first))⟩))
  · exact .inr (.inr (.inl ⟨.inr (.inr second),
      SourceCurrentNativeMuWriterOrigins.returned history terminal result owner cell (.inr (.inr second))⟩))
  · have actual := SourceCurrentNativeUnionWriterOrigins.left history owner terminal result cell closedLeft closedRight leftUnion row rowOrigin
    exact .inr (.inr (.inr (.inl ⟨leftUnion,by simpa only [Union,ite_true] using actual⟩)))
  · have actual := SourceCurrentNativeUnionWriterOrigins.right history owner terminal result cell closedLeft closedRight rightUnion row rowOrigin
    exact .inr (.inr (.inr (.inr ⟨rightUnion,by simpa only [Union,Bool.false_eq_true,ite_false] using actual⟩)))

/-- A literal completed query derives the same terminal origins and its actual final history. -/
theorem request {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before) (history : History before)
    (left : input.left.free = []) (right : input.right.free = [])
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      Resolved after input result rowIndex row := by
  obtain ⟨reached,checked,growth,origin⟩ := SourceCurrentSharedLeafNativeLineage.request input fuel result good history actual
  obtain ⟨handle,present,_⟩ := origin.returned left right
  exact ⟨reached,checked,growth,returned reached input result left right handle present rowIndex row selected⟩

end MicroCFTA.SourceCurrentNativeQueryTerminalOrigins
