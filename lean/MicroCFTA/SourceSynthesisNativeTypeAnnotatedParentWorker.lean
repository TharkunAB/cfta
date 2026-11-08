import MicroCFTA.SourceSynthesisNativeTypeAnnotatedLocalWorker
import MicroCFTA.SourceSynthesisNativeTypeParentHeap
import MicroCFTA.SourceSynthesisHereditaryMemoFields
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual
import MicroCFTA.SourceCurrentAllocatedLocalWorkerActual

/-!
# Complete Type rows at actual Parent returns

The resident input supplies its actual stored-field load. The same load
derives precheck and local work. The constructor retains the original Type
guard and adjusted children, or returns Top and the literal Empty sentinel.
The result retains the actual body, source reads and complete caller post.

Initial Context, Type state, closed annotated children, reached ranges and
successful execution remain premises. These laws do not establish failed
prefix preservation, all reached Type inputs, completion or driver bounds.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeAnnotatedParentWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisNativeTypeTrace (Origin origin_top)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryMemoFields (TypeRow)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "callerAdvance" => SourceCurrentAllocatedPartialState.advance
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
variable {width : Nat}

private theorem bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {result : B} {after : Checked width} {fourth : Fourth} {memo : Memo}
    (actual : first.bind next = .done result after fourth memo) :
    ∃ value middle saved warm, first = .done value middle saved warm ∧
      next value middle saved warm = .done result after fourth memo := by
  cases first with
  | done value middle saved warm => exact ⟨value, middle, saved, warm, rfl, actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem reduce_return {g s r e p h m c n budget loaded inherited children before fourth memo results after saved warm}
    (actual : SourceCurrentAllocatedParentWorker.reduceChildren (width := width) g s r e p h m c n budget
      loaded inherited children before fourth memo = .done results after saved warm) :
    SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children before fourth memo =
      .done results after saved warm := by
  cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children before fourth memo with
  | failed => simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at actual; cases actual
  | done value checked completed current =>
      simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at actual
      cases actual
      rfl

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem build_return {symbol loaded children before fourth memo result after saved warm}
    (actual : SourceCurrentAllocatedParentWorker.build (width := width) symbol loaded children before fourth memo =
      .done result after saved warm) :
    SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result, after) ∧
      saved = fourth ∧ warm = memo := by
  cases observed : SourceCurrentAllocatedMkEdge.build symbol loaded children before with
  | mk built checked =>
      cases built with
      | error => simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual; cases actual
      | ok value =>
          simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual
          cases actual
          exact ⟨rfl, rfl, rfl⟩

/-- The same successful Parent observation returns a complete annotated Type row. -/
theorem edge (lib : Library)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {before : Caller width} {memos : Memos} {request : Request}
    {g s r e p h m c n budget : Nat} {after : Checked width}
    {result : Edge} {savedFourth : Fourth} {saved : Memo}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge =
        .done result after savedFourth saved)
    (context : Context formulas solver inventory before memos)
    (ready : Ready lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before)
    (closed : ClosedValues request.value.children) (inputTypeRow : TypeRow lib request.value) :
    ∃ next final, ∃ body : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
        (callerAdvance before after savedFourth saved),
      SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver body memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
        (callerAdvance before after savedFourth saved) final ∧
      Post formulas solver next before (callerAdvance before after savedFourth saved) final ∧
      Ready lib (initialShared after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ TypeRow lib result := by
  obtain ⟨next, final, body, reads, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_verified
    formulas solver context inheritedReady resident ranges actual
  refine ⟨next, final, body, reads, receipt, post, ?_⟩
  cases rejected : contradictory request.value.entry.key.constraint with
  | true =>
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, ite_true] at actual
      cases actual
      have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
        request.value.entry.key.symbol before.checked context.ready context.admitted
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards⟩ :=
        SourceSynthesisNativeTypeParentHeap.reject lib constructor ready guards
      refine ⟨nextReady, extension, present, resultClosed, afterGuards, ?_, ?_⟩
      · rw [constructor.guard]
        exact origin_top lib
      · rw [constructor.children]
        intro child member
        cases List.mem_singleton.mp member
        exact .empty
  | false =>
      obtain ⟨cached, loaded, found⟩ := context.ready.good.fields request.value.entry.key request.value resident
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, Bool.false_eq_true, ite_false, found] at actual
      obtain ⟨children, middle, fourth, memo, reduced, built⟩ := bind_done _ _ actual
      have reduced := reduce_return reduced
      obtain ⟨constructed, sameFourth, sameMemo⟩ := build_return built
      subst fourth
      subst memo
      obtain ⟨own, branch, precheck⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
        before.checked context.ready context.admitted request.value.entry.key.constraint cached loaded found
        request.inherited inheritedReady
      obtain ⟨middleReady, first, _middleAvailable, middleClosed, middleGuards, middleTyped⟩ :=
        SourceSynthesisNativeTypeAnnotatedLocalWorker.reduce lib formulas solver precheck ready available closed guards
          inputTypeRow.2 (ranges rejected loaded found) reduced
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
        before.checked.operations.constraints context.ready.good.operations.constraints cached loaded found
      obtain ⟨chosenInventory, completedMemos, _graph, _reads, localReceipt⟩ := SourceCurrentAllocatedLocalWorkerActual.sound
        formulas solver context cached found inheritedReady available (ranges rejected loaded found) reduced
      have storedReady := loadedReady.1.grows localReceipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations
          (SourceEqualityConjoinAllocation.readback loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations request.value.entry.key.constraint
          from ⟨cached, loaded, found⟩).grows localReceipt.effects.grows
      obtain ⟨chosen, reached, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver chosenInventory
        request.value.entry.key.symbol loaded children middle localReceipt.ready localReceipt.admitted
        storedReady field localReceipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans constructed)
      cases Except.ok.inj same.1
      cases same.2
      obtain ⟨nextReady, last, present, resultClosed, afterGuards⟩ :=
        SourceSynthesisNativeTypeParentHeap.build lib constructor middleReady middleGuards middleClosed
      refine ⟨nextReady, first.trans last, present, resultClosed, afterGuards, ?_, ?_⟩
      · rw [constructor.guard]
        split
        · rw [loadedReady.2]
          exact inputTypeRow.1
        · exact origin_top lib
      · rw [constructor.children]
        split
        · exact middleTyped
        · intro child member
          cases List.mem_singleton.mp member
          exact .empty

end MicroCFTA.SourceSynthesisNativeTypeAnnotatedParentWorker
