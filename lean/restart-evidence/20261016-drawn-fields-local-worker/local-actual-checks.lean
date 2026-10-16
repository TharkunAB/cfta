import MicroCFTA.SourceCurrentAllocatedLocalWorkerActual

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.sound
#check @MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.sound
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.verified
#check @MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.finite
#check @MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.finite

namespace LocalActualChecks
open MicroCFTA
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt Ranges)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedLocalWorker (reduce)
open SourceCurrentAllocatedLocalWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : Inventory} {original : Guard} {g s r e p h m c n budget : Nat}
  {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
  {before : Caller width} {after : Checked width} {savedFourth : Fourth} {saved : Memo} {memos : Memos}
variable (initial : Context formulas solver inventory before memos)
  (cached : SourceEqualityGuardReadback.Cached original.equalities)
  (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
  (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
  (available : Values before.checked.native.machine.heap values)
  (ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge)
include initial cached found inheritedReady available ranges

theorem finite_literal_post :
    ∃ G S R E P H M C N output finalChecked fourth memo next final,
      reduce G S R E P H M C N budget loaded inherited values before.checked before.fourth before.merge =
        .done output finalChecked fourth memo ∧
      ∃ actual : Reduction budget loaded inherited values before.checked before.fourth before.merge
          output finalChecked fourth memo,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values output before.checked finalChecked
          before.fourth fourth before.merge memo final ∧
        Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before finalChecked fourth memo) final := by
  obtain ⟨output, finalChecked, fourth, memo, next, final, ⟨G, S, R, E, P, H, M, C, N, stable⟩,
    actual, reads, receipt, post⟩ := SourceCurrentAllocatedLocalWorkerActual.finite formulas solver
      budget original loaded inherited values initial cached found inheritedReady available ranges
  exact ⟨G, S, R, E, P, H, M, C, N, output, finalChecked, fourth, memo, next, final,
    stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    actual, reads, receipt, post⟩

theorem supplied_guarded_language
    (done : reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge =
      .done results after savedFourth saved) :
    InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap ∧ results.length = values.length ∧
      ∀ ambient symbol terms,
        (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
          All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
        (SourceEqualityPCSGuard.holds formulas solver original (.node symbol terms) = true →
          SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload →
          (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
            All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)) := by
  obtain ⟨_, _, _, _, receipt, post⟩ := SourceCurrentAllocatedLocalWorkerActual.verified
    formulas solver initial cached found inheritedReady available ranges done
  exact ⟨post.context.probes, receipt.length, receipt.language⟩

theorem warm_tables_same_context
    (done : reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge =
      .done results after savedFourth saved) :
    ∃ next final,
      Context formulas solver next (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
      (SourceCurrentAllocatedPartialState.advance before after savedFourth saved).nodeResults = before.nodeResults ∧
      (SourceCurrentAllocatedPartialState.advance before after savedFourth saved).edgeResults = before.edgeResults ∧
      Cache.Extends before.merge saved ∧ SourceCurrentEmptinessMemo.Extends before.fourth savedFourth := by
  obtain ⟨next, final, _, _, _, post⟩ := SourceCurrentAllocatedLocalWorkerActual.verified
    formulas solver initial cached found inheritedReady available ranges done
  exact ⟨next, final, post.context, rfl, rfl, post.retained, post.fourthRetained⟩

theorem empty_children_complete (empty : values = []) :
    ∃ finalChecked fourth memo next final,
      StableRun (fun G S R E P H M C N =>
        reduce G S R E P H M C N budget loaded inherited values before.checked before.fourth before.merge)
        [] finalChecked fourth memo ∧
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before finalChecked fourth memo) final := by
  obtain ⟨output, finalChecked, fourth, memo, next, final, stable, _, _, receipt, post⟩ :=
    SourceCurrentAllocatedLocalWorkerActual.finite formulas solver budget original loaded inherited values
      initial cached found inheritedReady available ranges
  have zero : output = [] := by
    cases output with
    | nil => rfl
    | cons head tail =>
        have impossible := receipt.length
        simp only [empty, List.length_nil, List.length_cons] at impossible
        omega
  subst output
  exact ⟨finalChecked, fourth, memo, next, final, stable, post⟩

theorem unchanged_zero_bounds
    (actual : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited
      before.checked.operations).1 = .ok .unchanged) :
    ∃ next final,
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before
          (SourceCurrentAllocatedPrecheck.state before.checked loaded inherited) before.fourth before.merge) final ∧
      reduce 0 0 0 0 0 0 0 0 0 budget loaded inherited values before.checked before.fourth before.merge =
        .done values (SourceCurrentAllocatedPrecheck.state before.checked loaded inherited) before.fourth before.merge := by
  have done := SourceCurrentAllocatedLocalWorker.reduce_unchanged 0 0 0 0 0 0 0 0 0 budget loaded inherited
    values before.checked before.fourth before.merge actual
  obtain ⟨next, final, _, _, _, post⟩ := SourceCurrentAllocatedLocalWorkerActual.verified
    formulas solver initial cached found inheritedReady available ranges done
  exact ⟨next, final, post, done⟩

theorem supplied_then_generated_query
    (done : reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge =
      .done results after savedFourth saved)
    (left right : Value Symbol Guard) (leftMember : left ∈ values) (rightMember : right ∈ values)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nextRanges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) after) :
    ∃ next fuel value finalChecked,
      SourceEqualityNativeDemand.execute (fuel + 1)
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) after =
        .done value finalChecked ∧
      At formulas solver next finalChecked ∧ value.free = [] ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term := by
  obtain ⟨localNext, _, _, _, receipt, post⟩ := SourceCurrentAllocatedLocalWorkerActual.verified
    formulas solver initial cached found inheritedReady available ranges done
  have ready := post.context.ready
  obtain ⟨next, fuel, value, finalChecked, _, _, query, admitted⟩ :=
    SourceCurrentAllocatedNativeInventoryState.query_complete localNext formulas solver after ready.good
      post.context.admitted ready.scopedCache ready.semantic ready.idle left right
      (receipt.originals left leftMember) (receipt.originals right rightMember) leftClosed rightClosed nextRanges
  exact ⟨next, fuel, value, finalChecked, query.toWarmReceipt.done, admitted, query.closed, query.meaning⟩

end LocalActualChecks

#print axioms LocalActualChecks.finite_literal_post
#check @LocalActualChecks.finite_literal_post
#print axioms LocalActualChecks.supplied_guarded_language
#check @LocalActualChecks.supplied_guarded_language
#print axioms LocalActualChecks.warm_tables_same_context
#check @LocalActualChecks.warm_tables_same_context
#print axioms LocalActualChecks.empty_children_complete
#check @LocalActualChecks.empty_children_complete
#print axioms LocalActualChecks.unchanged_zero_bounds
#check @LocalActualChecks.unchanged_zero_bounds
#print axioms LocalActualChecks.supplied_then_generated_query
#check @LocalActualChecks.supplied_then_generated_query
