import MicroCFTA.SourcePruningEnumerationObservation
import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourceCurrentAllocatedConjunctionCaller
import MicroCFTA.SourceCurrentConjunctionWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedConjunctionWorker
import MicroCFTA.SourceEndpointMemoCorrect

namespace MicroCFTA.SourcePruningEnumerationEnabledEmpty
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "reaches" => SourceEndpointReachability.reaches SourceMemoGate.unconstrained
variable {EnumGuard : Type} {width : Nat}

/-- Run the actual descendant memo before the enabled fourth-memo check. -/
noncomputable def check
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (queries : Queries) : SourceCurrentAllocatedConjunctionWorker.Outcome width × Queries :=
  let guardResult : Bool × Queries := SourceEndpointMemo.run query queries
  if guardResult.1 then
    (SourceCurrentAllocatedConjunctionWorker.call p h 1000 query before memo, guardResult.2)
  else (.done false before memo, guardResult.2)

/-- Derive the enabled replacement from two actual pending slots and the full input caller. -/
theorem pending_enabled_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (source target sourceHandle targetHandle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (memos : Memos) (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (sourceStored : before.values[source]? = some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated (some targetHandle) targetScs))
    (ranges : match lookupNode beforeCaller.checked.native.machine.heap sourceHandle,
        lookupNode beforeCaller.checked.native.machine.heap targetHandle with
      | some left, some right => SourceCurrentAllocatedNativeRequestBounds.WordRanges
          (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked
      | _, _ => True) :
    ∃ (left right : Node) (next : Inventory) (query : Node) (queried : Checked width)
      (reached answer : Bool) (guardSaved : Queries) (checkedAfter : Checked width)
      (saved : Fourth) (final : Memos) (replacement : Node) (handle p h : Nat),
      lookupNode beforeCaller.checked.native.machine.heap sourceHandle = some left ∧
      lookupNode beforeCaller.checked.native.machine.heap targetHandle = some right ∧
      next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
        beforeCaller.checked query queried memos ∧
      SourceEndpointMemo.run query memos.query = (reached, guardSaved) ∧
      SourceEndpointMemoCorrect.Checked queried.native.machine.heap memos.query (reaches query) (reached, guardSaved) ∧
      (∀ P H, p ≤ P → h ≤ H →
        check P H query queried beforeCaller.fourth memos.query = (.done answer checkedAfter saved, guardSaved)) ∧
      Post formulas solver next beforeCaller
        (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final ∧
      (reached = false → answer = false ∧ checkedAfter = queried ∧ saved = beforeCaller.fourth ∧
        final = {memos with query := guardSaved}) ∧
      (reached = true →
        ∃ reachedPhysical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula,
          checkedAfter = advancePhysical queried reachedPhysical ∧
          ∃ actual : SourceCurrentConjunctionMemo.Call 1000 beforeCaller.fourth query
              (physical queried) answer reachedPhysical saved,
            SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := guardSaved} final) ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Cache.Extends memos.unfolding final.unfolding ∧ final.query = guardSaved ∧
      replacement = (if answer then .empty else query) ∧
      Available checkedAfter.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode checkedAfter.native.machine.heap handle = some replacement ∧
      PendingRealized checkedAfter.native.machine.heap before ∧
      (∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term) := by
  obtain ⟨left, leftDecoded, leftAvailable, leftClosed⟩ :=
    realized source sourceHandle sourceScs sourceStored
  obtain ⟨right, rightDecoded, rightAvailable, rightClosed⟩ :=
    realized target targetHandle targetScs targetStored
  have decodedRanges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked := by
    simpa only [leftDecoded, rightDecoded] using ranges
  obtain ⟨next, query, queried, nextSource, nextRoots, receipt⟩ :=
    SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right beforeCaller.checked
      initial.ready initial.admitted leftAvailable rightAvailable leftClosed rightClosed decodedRanges
      memos initial.globals
  have queryProbes : InternedFreshOrdinaryProbeHeap.Heap queried.native.machine.heap := by
    cases receipt.actual with
    | run trace =>
        exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes
  cases guardRun : SourceEndpointMemo.run query memos.query with
  | mk reached guardSaved =>
    have guardChecked : SourceEndpointMemoCorrect.Checked queried.native.machine.heap
        memos.query (reaches query) (reached, guardSaved) := by
      simpa only [guardRun] using SourceEndpointMemoCorrect.run_checked query queried.native.machine.heap
        receipt.effects.keeps.ready.semantic.1.normal.facts.coherent receipt.available memos.query receipt.globals.query
    have queryContext : Context formulas solver next
        (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
        {memos with query := guardSaved} := by
      exact ⟨receipt.ready, receipt.admitted,
        initial.sound.advance formulas solver queried beforeCaller.fourth beforeCaller.merge receipt.effects,
        initial.stored.grows receipt.effects.keeps, initial.covered,
        SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps beforeCaller.fourth initial.correct,
        ⟨receipt.globals.unfolding, guardChecked.valid⟩, queryProbes⟩
    have queryPost : Post formulas solver next beforeCaller
        (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
        {memos with query := guardSaved} := by
      exact ⟨queryContext, receipt.effects, Cache.extends_refl _, fun key entry found => found⟩
    have phase : ∃ (answer : Bool) (checkedAfter : Checked width) (saved : Fourth)
        (final : Memos) (p h : Nat),
        (∀ P H, p ≤ P → h ≤ H →
          check P H query queried beforeCaller.fourth memos.query = (.done answer checkedAfter saved, guardSaved)) ∧
        Post formulas solver next
          (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
          (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final ∧
        (reached = false → answer = false ∧ checkedAfter = queried ∧ saved = beforeCaller.fourth ∧
          final = {memos with query := guardSaved}) ∧
        (reached = true →
          ∃ reachedPhysical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula,
            checkedAfter = advancePhysical queried reachedPhysical ∧
            ∃ actual : SourceCurrentConjunctionMemo.Call 1000 beforeCaller.fourth query
                (physical queried) answer reachedPhysical saved,
              SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := guardSaved} final) ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
        Available checkedAfter.native.machine.heap query ∧
        Cache.Extends memos.unfolding final.unfolding ∧ final.query = guardSaved := by
      cases reached with
      | false =>
          refine ⟨false, queried, beforeCaller.fourth, {memos with query := guardSaved}, 0, 0,
            ?_, Post.refl queryContext, ?_, ?_, ?_, receipt.available, Cache.extends_refl _, rfl⟩
          · intro P H enoughP enoughH
            simp only [check, guardRun, Bool.false_eq_true, ↓reduceIte]
          · intro notReached
            exact ⟨rfl, rfl, rfl, rfl⟩
          · intro isReached
            cases isReached
          · refine ⟨fun opened => rfl, ?_⟩
            intro impossible
            cases impossible
      | true =>
          obtain ⟨workerAnswer, workerPhysical, workerSaved, workerFinal, actualCall, actualReads,
            workerPost, workerSound, workerAvailable, workerUnfolding, workerQuerySame⟩ :=
            SourceCurrentAllocatedConjunctionCaller.finite formulas solver 1000 queryContext receipt.available
          obtain ⟨p, h, physicalStable⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete actualCall
          refine ⟨workerAnswer, advancePhysical queried workerPhysical, workerSaved, workerFinal, p, h,
            ?_, workerPost, ?_, ?_, workerSound, workerAvailable, workerUnfolding, workerQuerySame⟩
          · intro P H enoughP enoughH
            simp only [check, guardRun, ↓reduceIte]
            exact Prod.ext (SourceCurrentAllocatedConjunctionWorker.call_lift
              (physicalStable P H enoughP enoughH)) rfl
          · intro notReached
            cases notReached
          · intro isReached
            exact ⟨workerPhysical, rfl, actualCall, actualReads⟩
    obtain ⟨answer, checkedAfter, saved, final, p, h, stable, checkPost, skipped, performed,
      sound, queryAvailable, unfolding, querySame⟩ := phase
    have finalPost : Post formulas solver next beforeCaller
        (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final := by
      exact queryPost.trans checkPost
    have replacementFacts : Available checkedAfter.native.machine.heap (if answer then .empty else query) ∧
        (if answer then .empty else query).free = [] ∧
        (∀ ambient term,
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient
            (if answer then .empty else query) term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term) := by
      cases answer with
      | false =>
          exact ⟨queryAvailable, receipt.closed, fun ambient term => Iff.rfl⟩
      | true =>
          refine ⟨empty_available _, rfl, ?_⟩
          intro ambient term
          constructor
          · intro accepted
            simp only [↓reduceIte, InternedGuardedLanguage.meaning] at accepted
          · intro accepted
            exact False.elim (sound.2 rfl ambient term accepted)
    obtain ⟨replacementAvailable, replacementClosed, replacementMeaning⟩ := replacementFacts
    obtain ⟨handle, encoded, decoded⟩ := available_readback checkedAfter.native.machine.heap
      (if answer then .empty else query) finalPost.effects.keeps.ready.semantic.1.normal.facts.coherent
      replacementAvailable replacementClosed
    have finalRealized : PendingRealized checkedAfter.native.machine.heap before := by
      exact realized_preserved beforeCaller.checked.native.machine.heap checkedAfter.native.machine.heap
        before before realized (EnumerationCompressionFrame.Frame.refl before) finalPost.effects.keeps
    exact ⟨left, right, next, query, queried, reached, answer, guardSaved, checkedAfter, saved,
      final, (if answer then .empty else query), handle, p, h,
      leftDecoded, rightDecoded, nextSource, nextRoots, receipt, guardRun, guardChecked, stable,
      finalPost, skipped, performed, sound, unfolding, querySame, rfl,
      replacementAvailable, replacementClosed, encoded, decoded, finalRealized,
      fun ambient term => (replacementMeaning ambient term).trans (receipt.meaning ambient term)⟩

end MicroCFTA.SourcePruningEnumerationEnabledEmpty
