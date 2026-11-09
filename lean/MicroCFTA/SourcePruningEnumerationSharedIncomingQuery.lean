import MicroCFTA.SourcePruningEnumerationSharedEnabledEmptyActual
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionCallerCompletion
import MicroCFTA.SourcePruningEnumerationObservation
import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourceEndpointMemoCorrect

/-!
# Incoming queries with actual enabled shared checks

The native intersection runs first. The optional descendant memo then selects
an actual shared check or a skip. Current caller facts derive one successful
observation and its exact checked state, fourth memo and ordered global reads.
Larger observation bounds retain that same enabled outcome and private state.

A skipped branch has no shared snapshot or shared read receipt. The receipt
for a performed branch belongs to its actual base bounds. This theorem keeps
the existing native word-range premise and does not select a driver policy.
-/

namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
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
local notation "Observed" => SourcePruningEnumerationSharedEnabledEmpty.Outcome
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "reaches" => SourceEndpointReachability.reaches SourceMemoGate.unconstrained
variable {width : Nat}

/-- Construct one checked intersection and its optional sound Empty replacement. -/
theorem complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (left right : Node) (checkEmpty : Bool) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (leftAvailable : Available beforeCaller.checked.native.machine.heap left)
    (rightAvailable : Available beforeCaller.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked) :
    ∃ (next : Inventory) (query : Node) (queried : Checked width)
      (answer : Bool) (checkedAfter : Checked width) (saved : Fourth)
      (final : Memos) (queries : Queries) (replacement : Node) (handle fuel p h : Nat)
      (observed : Observed width),
      next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
        beforeCaller.checked query queried memos ∧
      (∀ extra, SourceEqualityNativeDemand.execute (fuel + extra)
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
        beforeCaller.checked = .done query queried) ∧
      (∀ P H, p ≤ P → h ≤ H →
        (if checkEmpty then
          SourcePruningEnumerationSharedEnabledEmpty.check P H query queried beforeCaller.fourth memos.query
        else (.skipped queried beforeCaller.fourth, memos.query)) =
          (observed, queries)) ∧
      observed.completed = some answer ∧ observed.state = checkedAfter ∧ observed.memo = saved ∧
      Post formulas solver next beforeCaller
        (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final ∧
      final.query = queries ∧ Cache.Extends memos.unfolding final.unfolding ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      replacement = (if answer then .empty else query) ∧
      Available checkedAfter.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode checkedAfter.native.machine.heap handle = some replacement ∧
      (∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term) ∧
      (checkEmpty = false → answer = false ∧ replacement = query ∧ checkedAfter = queried ∧
        saved = beforeCaller.fourth ∧ queries = memos.query ∧ final = memos) ∧
      (checkEmpty = true → ∃ reached,
        SourceEndpointMemo.run query memos.query = (reached, queries) ∧
        SourceEndpointMemoCorrect.Checked queried.native.machine.heap memos.query
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained query) (reached, queries) ∧
        (reached = false → answer = false ∧ checkedAfter = queried ∧ saved = beforeCaller.fourth ∧
          final = {memos with query := queries}) ∧
        (reached = true → ∃ (baseP baseH : Nat) (snapshot : Snapshot),
          SourceCurrentAllocatedSharedConjunctionWorker.call baseP baseH
              SourceCurrentConjunctionTupleBudget.currentTupleBudget query queried beforeCaller.fourth =
            .done answer checkedAfter saved snapshot ∧
          SourceCurrentConjunctionSharedWorkerOutcomeMemos.CallReads baseP baseH
            SourceCurrentConjunctionTupleBudget.currentTupleBudget beforeCaller.fourth query
            (physical queried) {memos with query := queries} final)) := by
  obtain ⟨next, query, queried, nextSource, nextRoots, receipt⟩ :=
    SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right beforeCaller.checked
      initial.ready initial.admitted leftAvailable rightAvailable leftClosed rightClosed ranges memos initial.globals
  obtain ⟨fuel, nativeDone⟩ := receipt.actual.done
  have queryProbes : InternedFreshOrdinaryProbeHeap.Heap queried.native.machine.heap := by
    cases receipt.actual with
    | @run traceFuel trace =>
        exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes
  have queryContext : Context formulas solver next
      (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge) memos := by
    exact ⟨receipt.ready, receipt.admitted,
      initial.sound.advance formulas solver queried beforeCaller.fourth beforeCaller.merge receipt.effects,
      initial.stored.grows receipt.effects.keeps, initial.covered,
      SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps beforeCaller.fourth initial.correct,
      receipt.globals, queryProbes⟩
  have queryPost : Post formulas solver next beforeCaller
      (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge) memos := by
    exact ⟨queryContext, receipt.effects, Cache.extends_refl _, fun key entry found => found⟩
  cases checkEmpty with
  | false =>
      obtain ⟨handle, encoded, decoded⟩ := available_readback queried.native.machine.heap query
        receipt.effects.keeps.ready.semantic.1.normal.facts.coherent receipt.available receipt.closed
      refine ⟨next, query, queried, false, queried, beforeCaller.fourth, memos, memos.query,
        query, handle, fuel, 0, 0, .skipped queried beforeCaller.fourth,
        nextSource, nextRoots, receipt, ?_, ?_, rfl, rfl, rfl, queryPost, rfl,
        Cache.extends_refl _, ?_, rfl, receipt.available, receipt.closed, encoded, decoded,
        receipt.meaning, ?_, ?_⟩
      · intro extra
        exact SourceEqualityNativeDemand.done_stable fuel extra _ beforeCaller.checked queried query nativeDone
      · intro P H enoughP enoughH
        simp only [Bool.false_eq_true, ↓reduceIte]
      · refine ⟨fun opened => rfl, ?_⟩
        intro impossible
        cases impossible
      · intro disabled
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro enabled
        cases enabled
  | true =>
    cases guardRun : SourceEndpointMemo.run query memos.query with
    | mk reached guardSaved =>
      have guardChecked : SourceEndpointMemoCorrect.Checked queried.native.machine.heap
          memos.query (reaches query) (reached, guardSaved) := by
        simpa only [guardRun] using SourceEndpointMemoCorrect.run_checked query queried.native.machine.heap
          receipt.effects.keeps.ready.semantic.1.normal.facts.coherent receipt.available memos.query receipt.globals.query
      have guardContext : Context formulas solver next
          (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
          {memos with query := guardSaved} := by
        exact ⟨queryContext.ready, queryContext.admitted, queryContext.sound, queryContext.stored,
          queryContext.covered, queryContext.correct,
          ⟨receipt.globals.unfolding, guardChecked.valid⟩, queryContext.probes⟩
      have guardPost : Post formulas solver next beforeCaller
          (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
          {memos with query := guardSaved} := by
        exact ⟨guardContext, receipt.effects, Cache.extends_refl _, fun key entry found => found⟩
      have phase : ∃ (answer : Bool) (checkedAfter : Checked width) (saved : Fourth)
          (final : Memos) (p h : Nat) (observed : Observed width),
          (∀ P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationSharedEnabledEmpty.check P H query queried beforeCaller.fourth memos.query =
              (observed, guardSaved)) ∧
          observed.completed = some answer ∧ observed.state = checkedAfter ∧ observed.memo = saved ∧
          Post formulas solver next
            (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
            (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final ∧
          (reached = false → answer = false ∧ checkedAfter = queried ∧ saved = beforeCaller.fourth ∧
            final = {memos with query := guardSaved}) ∧
          (reached = true → ∃ (baseP baseH : Nat) (snapshot : Snapshot),
            SourceCurrentAllocatedSharedConjunctionWorker.call baseP baseH
                SourceCurrentConjunctionTupleBudget.currentTupleBudget query queried beforeCaller.fourth =
              .done answer checkedAfter saved snapshot ∧
            SourceCurrentConjunctionSharedWorkerOutcomeMemos.CallReads baseP baseH
              SourceCurrentConjunctionTupleBudget.currentTupleBudget beforeCaller.fourth query
              (physical queried) {memos with query := guardSaved} final) ∧
          SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
          Available checkedAfter.native.machine.heap query ∧
          Cache.Extends memos.unfolding final.unfolding ∧ final.query = guardSaved := by
        cases reached with
        | false =>
            refine ⟨false, queried, beforeCaller.fourth, {memos with query := guardSaved}, 0, 0,
              .skipped queried beforeCaller.fourth, ?_, rfl, rfl, rfl,
              Post.refl guardContext, ?_, ?_, ?_, receipt.available, Cache.extends_refl _, rfl⟩
            · intro P H enoughP enoughH
              exact SourcePruningEnumerationSharedEnabledEmpty.check_skipped
                P H query queried beforeCaller.fourth memos.query guardSaved guardRun
            · intro notReached
              exact ⟨rfl, rfl, rfl, rfl⟩
            · intro isReached
              cases isReached
            · refine ⟨fun opened => rfl, ?_⟩
              intro impossible
              cases impossible
        | true =>
            obtain ⟨workerAnswer, workerChecked, workerSaved, snapshot, workerFinal, p, h,
                actualCall, actualReads, workerPost, workerSound, workerAvailable,
                workerUnfolding, workerQuerySame, workerStable⟩ :=
              SourceCurrentAllocatedSharedConjunctionCaller.finite formulas solver
                SourceCurrentConjunctionTupleBudget.currentTupleBudget guardContext receipt.available
            refine ⟨workerAnswer, workerChecked, workerSaved, workerFinal, p, h,
              .performed (.done workerAnswer workerChecked workerSaved snapshot),
              ?_, rfl, rfl, rfl, workerPost, ?_, ?_, workerSound, workerAvailable,
              workerUnfolding, workerQuerySame⟩
            · intro P H enoughP enoughH
              rw [SourcePruningEnumerationSharedEnabledEmpty.check_performed
                P H query queried beforeCaller.fourth memos.query guardSaved guardRun]
              exact Prod.ext (congrArg SourcePruningEnumerationSharedEnabledEmpty.Outcome.performed
                (workerStable P H enoughP enoughH)) rfl
            · intro notReached
              cases notReached
            · intro isReached
              exact ⟨p, h, snapshot, actualCall, actualReads⟩
      obtain ⟨answer, checkedAfter, saved, final, p, h, observed, stable, completed, observedState,
        observedMemo, checkPost, skipped, performed, sound, queryAvailable, unfolding, querySame⟩ := phase
      have finalPost : Post formulas solver next beforeCaller
          (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final := by
        exact guardPost.trans checkPost
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
      refine ⟨next, query, queried, answer, checkedAfter, saved, final, guardSaved,
        (if answer then .empty else query), handle, fuel, p, h, observed, nextSource, nextRoots, receipt,
        ?_, ?_, completed, observedState, observedMemo, finalPost, querySame, unfolding, sound, rfl, replacementAvailable,
        replacementClosed, encoded, decoded, ?_, ?_, ?_⟩
      · intro extra
        exact SourceEqualityNativeDemand.done_stable fuel extra _ beforeCaller.checked queried query nativeDone
      · intro P H enoughP enoughH
        simpa only [↓reduceIte] using stable P H enoughP enoughH
      · intro ambient term
        exact (replacementMeaning ambient term).trans (receipt.meaning ambient term)
      · intro disabled
        cases disabled
      · intro enabled
        exact ⟨reached, guardRun, guardChecked, skipped, performed⟩

end MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
