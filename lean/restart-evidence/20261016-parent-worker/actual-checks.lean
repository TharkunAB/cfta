import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.LiveInputs
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.LiveInputs
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.ResidentRanges
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.ResidentRanges
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.finite
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.finite
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.verified
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.sound
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.sound
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.rejected_finite
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.rejected_finite
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.resident_finite
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.resident_finite
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerActual.resident_verified
#check @MicroCFTA.SourceCurrentAllocatedParentWorkerActual.resident_verified

namespace ParentActualChecks
open MicroCFTA
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedParentWorker (edge)
open SourceCurrentAllocatedParentWorkerActual (LiveInputs ResidentRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem rejection_without_live_inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue) (values : List (Value Symbol Guard))
    (initial : Context formulas solver inventory before memos) (test : contradictory original = true) :
    ∃ next final,
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2
          before.fourth before.merge) final ∧
      Resident (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2.native.machine.heap
        (SourceCurrentAllocatedMkEdge.reject symbol before.checked).1 ∧
      edge 0 0 0 0 0 0 0 0 0 budget symbol original inherited values before.checked before.fourth before.merge =
        .done (SourceCurrentAllocatedMkEdge.reject symbol before.checked).1
          (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2 before.fourth before.merge := by
  obtain ⟨_, result, after, fourth, memo, next, final, ⟨G, S, R, E, P, H, M, C, N, stable⟩,
    _, _, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.rejected_finite
      formulas solver budget symbol original inherited values initial test
  have done := SourceCurrentAllocatedParentWorker.edge_rejected 0 0 0 0 0 0 0 0 0 budget symbol original inherited
    values before.checked before.fourth before.merge test
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedParentWorkerStability.edge_done_unique
    (stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  exact ⟨next, final, post, receipt.resident, done⟩

theorem raw_finite_strict_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (initial : Context formulas solver inventory before memos)
    (live : LiveInputs budget original loaded inherited values before) :
    ∃ G S R E P H M C N result after fourth memo next final,
      edge G S R E P H M C N budget symbol original inherited values before.checked before.fourth before.merge =
        .done result after fourth memo ∧
      ∃ actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values
          before.checked before.fourth before.merge result after fourth memo,
        SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after fourth memo) final ∧
        InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap := by
  obtain ⟨result, after, fourth, memo, next, final, ⟨G, S, R, E, P, H, M, C, N, stable⟩,
    actual, reads, _, post⟩ := SourceCurrentAllocatedParentWorkerActual.finite
      formulas solver budget symbol original loaded inherited values initial live
  exact ⟨G, S, R, E, P, H, M, C, N, result, after, fourth, memo, next, final,
    stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    actual, reads, post, post.context.probes⟩

theorem resident_finite_actual_body
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : ResidentRanges budget request before) :
    ∃ G S R E P H M C N result after fourth memo next final,
      edge G S R E P H M C N budget request.value.entry.key.symbol request.value.entry.key.constraint
        request.inherited request.value.children before.checked before.fourth before.merge = .done result after fourth memo ∧
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
          (SourceCurrentAllocatedPartialState.advance before after fourth memo),
        SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after fourth memo) final ∧
        SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
  obtain ⟨result, after, fourth, memo, next, final, ⟨G, S, R, E, P, H, M, C, N, stable⟩,
    actual, reads, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_finite
      formulas solver budget request initial inheritedReady resident ranges
  exact ⟨G, S, R, E, P, H, M, C, N, result, after, fourth, memo, next, final,
    stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    actual, reads, post, receipt.language⟩

theorem supplied_resident_law
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget g s r e p h m c n : Nat} {request : Request}
    {before : Caller width} {after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth : Fourth} {memo : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : ResidentRanges budget request before)
    (done : edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge = .done result after fourth memo) :
    Resident after.native.machine.heap result ∧
      InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap ∧
      SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result ∧
      Cache.Extends before.merge memo ∧ SourceCurrentEmptinessMemo.Extends before.fourth fourth := by
  obtain ⟨_, _, _, _, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_verified
    formulas solver initial inheritedReady resident ranges done
  exact ⟨receipt.resident, post.context.probes, receipt.language, post.retained, post.fourthRetained⟩

theorem live_missing_field_stays_incomplete
    (budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (test : contradictory original = false)
    (missing : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok none) :
    edge 0 0 0 0 0 0 0 0 0 budget symbol original inherited values before fourth memo =
      .failed .missingField before fourth memo :=
  SourceCurrentAllocatedParentWorker.edge_missing_field 0 0 0 0 0 0 0 0 0 budget symbol original inherited
    values before fourth memo test missing

theorem resident_then_generated_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget g s r e p h m c n : Nat} {request : Request}
    {before : Caller width} {after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth : Fourth} {memo : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : ResidentRanges budget request before)
    (done : edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge = .done result after fourth memo)
    (left right : Value Symbol Guard) (leftMember : left ∈ request.value.children) (rightMember : right ∈ request.value.children)
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
  obtain ⟨parentNext, _, _, _, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_verified
    formulas solver initial inheritedReady resident ranges done
  have children := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  have ready := post.context.ready
  obtain ⟨next, fuel, value, finalChecked, _, _, query, admitted⟩ :=
    SourceCurrentAllocatedNativeInventoryState.query_complete parentNext formulas solver after ready.good
      post.context.admitted ready.scopedCache ready.semantic ready.idle left right
      (receipt.effects.keeps.available left (children left leftMember))
      (receipt.effects.keeps.available right (children right rightMember)) leftClosed rightClosed nextRanges
  exact ⟨next, fuel, value, finalChecked, query.toWarmReceipt.done, admitted, query.closed, query.meaning⟩

end ParentActualChecks

#print axioms ParentActualChecks.rejection_without_live_inputs
#check @ParentActualChecks.rejection_without_live_inputs
#print axioms ParentActualChecks.raw_finite_strict_post
#check @ParentActualChecks.raw_finite_strict_post
#print axioms ParentActualChecks.resident_finite_actual_body
#check @ParentActualChecks.resident_finite_actual_body
#print axioms ParentActualChecks.supplied_resident_law
#check @ParentActualChecks.supplied_resident_law
#print axioms ParentActualChecks.live_missing_field_stays_incomplete
#check @ParentActualChecks.live_missing_field_stays_incomplete
#print axioms ParentActualChecks.resident_then_generated_query
#check @ParentActualChecks.resident_then_generated_query
