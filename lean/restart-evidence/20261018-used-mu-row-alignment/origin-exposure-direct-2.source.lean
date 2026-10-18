import MicroCFTA.SourceCurrentNativeOpenQueryRowOrigins
import MicroCFTA.SourceCurrentNativeMuBodyOrigins
import MicroCFTA.MergedFreshOrdinaryGraphOrigins

/-!
# Actual native writers at complete epsilon origins

A complete origin derives the native request codecs without closed inputs.
The terminal receipt retains one actual captured writer. Its Mu body uses
that same writer interval. A retained Mu exposes its actual stored-body
execution at the reader. The origin tail keeps the original reader view.
No relation to a prospective callback or initial operand is assumed.
-/
namespace MicroCFTA.SourceCurrentNativeOriginExposure
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeQueryRowOrigins (Route)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionControl (decision)
open MergedFreshOrdinaryGraph (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual stored unfolding retains its full execution and an origin at the original reader view. -/
def Unfold (reader : Heap) (entry : Interned InternedBinderProtocol.NodeKey)
    (storedBody depth ordinary : Value Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ value after,
    InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry storedBody depth ordinary) reader =
      .done value after ∧
    InternedFreshOrdinaryStoredSubstitution.execute storedBody
      (fun name => if name = .interned entry.identity then some (.mu entry storedBody depth ordinary) else none)
      reader = .done value after ∧
    InternedConstructorTemplates.Valid after ∧ Grows reader after ∧ Origin reader [value] row

/-- A complete Mu origin supplies a successful actual stored unfolding without a completion premise. -/
theorem unfold_origin (reader : Heap) (valid : InternedConstructorTemplates.Valid reader)
    (entry : Interned InternedBinderProtocol.NodeKey) (storedBody depth ordinary : Value Symbol Guard)
    (row : EdgeValue Symbol Guard) (origin : Origin reader [.mu entry storedBody depth ordinary] row) :
    Unfold reader entry storedBody depth ordinary row := by
  have delegated := (MergedFreshOrdinaryGraph.origin_expand reader _ rfl row).mp origin
  cases actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry storedBody depth ordinary) reader with
  | pending key after =>
      have impossible : Origin reader [] row := by
        simpa only [MergedFreshOrdinaryGraph.successors,actual] using delegated
      obtain ⟨value,member,_⟩ := (MergedFreshOrdinaryGraph.origin_seeds reader [] row).mp impossible
      cases member
  | done value after =>
      have correct := InternedFreshOrdinaryStoredSubstitution.unfold_correct
        (.mu entry storedBody depth ordinary) reader valid
      have facts : InternedConstructorTemplates.Valid after ∧ Grows reader after := by
        simpa only [actual,InternedNestedConstruction.Outcome.state] using correct
      exact ⟨value,after,actual,actual,facts.1,facts.2,
        (MergedFreshOrdinaryGraph.origin_unfold reader entry storedBody depth ordinary value after actual row).mp origin⟩

/-- Any complete result origin derives both input codecs and the actual native request key. -/
theorem keyable {before after : Checked width} (request : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure result)) after)
    (view : Heap) (row : EdgeValue Symbol Guard) (origin : Origin view [result] row) :
    ∃ first second key,
      IntersectionFlatMemoKey.input request.left.referenceOf = some first ∧
      IntersectionFlatMemoKey.input request.right.referenceOf = some second ∧
      SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  have keyed : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right ≠ none := by
    intro missing
    have empty := SourceCurrentNativeRowKeyable.unkeyed_empty request fuel result missing actual
    exact MergedFreshOrdinaryGraph.origin_empty view row (empty ▸ origin)
  cases left : IntersectionFlatMemoKey.input request.left.referenceOf with
  | none =>
      exact (keyed (by simp [SourceRecursiveIntersectionMemo.requestKey,
        IntersectionFlatMemoKeyDomain.sourceKey,IntersectionFlatMemoKey.key,left])).elim
  | some first =>
      cases right : IntersectionFlatMemoKey.input request.right.referenceOf with
      | none =>
          exact (keyed (by simp [SourceRecursiveIntersectionMemo.requestKey,
            IntersectionFlatMemoKeyDomain.sourceKey,IntersectionFlatMemoKey.key,left,right])).elim
      | some second =>
          exact ⟨first,second,_,rfl,rfl,
            IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ first second left right⟩

/-- One captured native writer retains its literal interval and its own conditional Mu body receipt. -/
def Writer (reader : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Value Symbol Guard) : Prop :=
  ∃ (before after : Checked width) (fuel : Nat),
    Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
      {after with native := finishNode handle result after.native} ∧
    Grows before.native.machine.heap reader.native.machine.heap ∧
    Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
    ((decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu) →
      SourceCurrentNativeMuBodyOrigins.Body reader fuel request before result after)

/-- An actual returned cell retains its terminal writer and any retained Mu's actual epsilon execution. -/
theorem returned {reader : Checked width} (history : History reader) (good : Good reader)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (present : ∃ handle,reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (row : EdgeValue Symbol Guard) (origin : Origin reader.native.machine.heap [result] row) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
      (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
      Writer reader handle terminal result ∧
      ∀ entry body depth ordinary, result = .mu entry body depth ordinary →
        Unfold reader.native.machine.heap entry body depth ordinary row := by
  obtain ⟨terminal,handle,route,cell,writer,notSwap,notReset,first,second⟩ :=
    SourceCurrentNativeOpenQueryForwarding.normalize history request result left right present
  obtain ⟨before,after,fuel,checked,ready,started,actual,kept,finish,firstGrowth,lastGrowth,retained⟩ := writer
  refine ⟨terminal,handle,route,cell,notSwap,notReset,first,second,
    ⟨before,after,fuel,checked,ready,started,actual,kept,finish,firstGrowth,lastGrowth,retained,?_⟩,?_⟩
  · intro selected
    have compiled : compileNode terminal = compileMu terminal.domain terminal.left terminal.right := by
      rcases selected with selected | selected | selected <;> simp only [compileNode,selected]
    exact SourceCurrentNativeMuBodyOrigins.trace history terminal fuel result checked (compiled ▸ actual) retained
  · intro entry body depth ordinary same
    exact unfold_origin reader.native.machine.heap good.heap.semantic.1.normal.facts.coherent.valid
      entry body depth ordinary row (same ▸ origin)

/-- An actual request with a complete origin derives its terminal writer and retained Mu exposure. -/
theorem request {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after)
    (row : EdgeValue Symbol Guard) (origin : Origin after.native.machine.heap [result] row) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      ∃ terminal handle, Route after result input terminal ∧
        after.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
        decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
        decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
        (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
        (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
        Writer after handle terminal result ∧
        ∀ entry body depth ordinary, result = .mu entry body depth ordinary →
          Unfold after.native.machine.heap entry body depth ordinary row := by
  obtain ⟨first,second,key,left,right,keyed⟩ := keyable input fuel result actual _ row origin
  obtain ⟨reached,checked,growth,observed⟩ :=
    SourceCurrentSharedLeafNativeLineage.request input fuel result good history actual
  have present : ∃ handle,after.native.nodes.cells handle = some ⟨input,.returned result⟩ := by
    rcases observed with ⟨missing,_⟩ | ⟨handle,cell,_⟩
    · rw [keyed] at missing
      cases missing
    · exact ⟨handle,cell⟩
  exact ⟨reached,checked,growth,returned reached checked input result ⟨first,left⟩ ⟨second,right⟩ present row origin⟩

end MicroCFTA.SourceCurrentNativeOriginExposure
