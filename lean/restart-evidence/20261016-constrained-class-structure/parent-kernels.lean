import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParent
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReturned
import MicroCFTA.SourceCurrentAllocatedPartialGraph
import MicroCFTA.SourceCurrentAllocatedPartialMemoSound
namespace FiniteOrdinaryParentKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialState (EdgeRequest beginEdge finishEdge initial advance)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "ReturnedStored" => SourceCurrentAllocatedFiniteOrdinaryReturned.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)

/-- An actual finite parent produces the certificate installed at its exact published outer owner. -/
theorem finite_parent_publication (budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap original.children) (domain : Domain original)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedParentEdge.Ranges budget original.entry.key.constraint loaded inherited original.children before fourth memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    let request : EdgeRequest := ⟨inherited, original⟩
    let cold := initial before memo fourth
    ∃ result after savedFourth saved next final, ∃ finished : Caller width,
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo)
        result after savedFourth saved ∧
      SourceCurrentAllocatedParentEdge.Receipt formulas solver next original.entry.key.symbol original.entry.key.constraint
        loaded inherited original.children before result after fourth savedFourth memo saved final ∧
      SourceCurrentAllocatedPartialGraph.EdgeCall budget request cold result finished ∧
      finished = finishEdge 0 result (advance (beginEdge request cold).2.2 after savedFourth saved) ∧
      ReturnedStored finished ∧ EdgeNarrow original result ∧
      finished.edgeResults.cells 0 = some ⟨request, .returned result⟩ ∧
      beginEdge request finished = (0, .ready result, finished) ∧
      finished.checked = after ∧ finished.fourth = savedFourth ∧ finished.merge = saved ∧
      ∀ child ∈ result.children, SourceCurrentAllocatedFiniteOrdinaryDomain.Node child ∧
        SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨inherited, child⟩ <
          SourceCurrentAllocatedPartialActiveOrder.edgeRank request := by
  let request : EdgeRequest := ⟨inherited, original⟩
  let cold := initial before memo fourth
  let running := (beginEdge request cold).2.2
  have fresh := SourceCurrentAllocatedPartialMemoSound.beginEdge_fresh request cold rfl
  have started : beginEdge request cold = (0, .evaluate request, running) := by
    apply Prod.ext
    · exact congrArg Prod.fst fresh.1
    · apply Prod.ext
      · exact congrArg (fun pair => pair.2.1) fresh.1
      · rfl
  have runningCell : running.edgeResults.cells 0 = some ⟨request, .evaluating⟩ := fresh.2
  obtain ⟨result, after, savedFourth, saved, next, final, stable, actual, _, receipt, _, _, narrowed⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParent.finite formulas solver inventory budget original loaded inherited before fourth memo
      ready admitted cached found inheritedReady available domain correct physical covered ranges native merged memos valid
  let completed := advance running after savedFourth saved
  let finished := finishEdge 0 result completed
  have body : SourceCurrentAllocatedPartialGraph.EdgeBody budget request running result completed :=
    .parent (fun _ => found) actual
  have graph : SourceCurrentAllocatedPartialGraph.EdgeCall budget request cold result finished := .evaluate started body
  have storedCold := SourceCurrentAllocatedFiniteOrdinaryReturned.initial before memo fourth
  have storedRunning := storedCold.beginEdge request
  have storedCompleted := storedRunning.advance after savedFourth saved
  have returnedStored : ReturnedStored finished := storedCompleted.finishEdge result runningCell (fun _ => narrowed)
  have returned : finished.edgeResults.cells 0 = some ⟨request, .returned result⟩ :=
    SourceCurrentAllocatedPartialState.finishEdge_returned 0 request result completed runningCell
  have published : finished.edgeResults.table request.key = some 0 := by
    simp [finished, completed, running, cold, finishEdge, advance, beginEdge, initial,
      FlatMemoThunk.finish, FlatMemoThunk.lookupOrInsert, FlatMemoThunk.demand, FlatMemoThunk.empty,
      FlatMemoThunk.setStatus, put]
  have hit := SourceCurrentAllocatedPartialState.beginEdge_ready request request finished 0 result published returned
  exact ⟨result, after, savedFourth, saved, next, final, finished, stable, receipt, graph, rfl,
    returnedStored, narrowed, returned, hit, rfl, rfl, rfl,
    fun child member => returnedStored.child returned domain inherited child member⟩

/-- Raw rejection derives a stable sentinel of height zero without original-domain or child inputs. -/
theorem raw_rejected (budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before)
    (test : SourceEqualityMkEdgeAllocation.contradictory original.entry.key.constraint = true)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    let result := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
    let after := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2
    SourceCurrentAllocatedParentWorkerCompletion.StableRun
      (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
        original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo)
      result after fourth memo ∧ NativeStored after.native ∧ MergeStored memo ∧ EdgeNarrow original result ∧
      result.children = [.empty] ∧ MergedOrdinaryHeight.edgeHeight result = 0 := by
  obtain ⟨stable, _, _, _, nativeAfter, mergeAfter, narrowed⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParent.rejected_finite formulas solver inventory budget original loaded inherited before fourth memo
      ready admitted test correct physical covered native merged memos valid
  have receipt := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory original.entry.key.symbol before ready admitted
  refine ⟨stable, nativeAfter, mergeAfter, narrowed, receipt.children, ?_⟩
  rw [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children, receipt.children]
  rfl
end FiniteOrdinaryParentKernels
#print axioms FiniteOrdinaryParentKernels.finite_parent_publication
#check @FiniteOrdinaryParentKernels.finite_parent_publication
#print axioms FiniteOrdinaryParentKernels.raw_rejected
#check @FiniteOrdinaryParentKernels.raw_rejected
