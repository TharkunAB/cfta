import MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedParentWorkerStability
import MicroCFTA.SourceCurrentAllocatedPartialEdgeActual
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Full caller receipts for literal checked parent reduction

Raw rejection needs no field, inherited, child, or local range premise.
Only a live branch uses the original field in its actual initial cache.
Resident edge inputs derive that field and child residency from readiness.
Stable execution and success uniqueness retain the same complete return.
The actual strict reads derive probes and the full returned caller.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentWorkerActual
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedParentEdge (Edge Receipt)
open SourceCurrentAllocatedParentEdgeActual (Reads)
open SourceCurrentAllocatedParentWorker (edge)
open SourceCurrentAllocatedParentWorkerCompletion (StableRun)
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

/-- Only a reached live branch needs the existing field, original children, and local checks. -/
def LiveInputs (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller width) : Prop :=
  contradictory original = false →
    SourceEqualityGuardReadback.Cached original.equalities ∧
    SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded) ∧
    SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited ∧
    Values before.checked.native.machine.heap values ∧
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before.checked before.fourth before.merge

/-- The resident range plan selects only a live field loaded from the actual initial cache. -/
def ResidentRanges (budget : Nat) (request : Request) (before : Caller width) : Prop :=
  contradictory request.value.entry.key.constraint = false →
    ∀ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
        .ok (some loaded) →
      SourceCurrentAllocatedLocalReduction.Ranges budget loaded request.inherited request.value.children
        before.checked before.fourth before.merge

private theorem caller_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory next : Inventory} {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated}
    {inherited : EqValue} {values : List (Value Symbol Guard)} {before : Caller width}
    {after : Checked width} {result : EdgeValue Symbol Guard} {savedFourth : Fourth} {saved : Memo} {memos final : Memos}
    {actual : Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
      result after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (initial : Context formulas solver inventory before memos)
    (live : LiveInputs budget original loaded inherited values before)
    (receipt : Receipt formulas solver next symbol original loaded inherited values before.checked result after
      before.fourth savedFourth before.merge saved final) :
    Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  have probes := SourceCurrentAllocatedProbeParent.parent_heap formulas solver inventory reads initial.ready initial.admitted
    (fun test => ⟨(live test).1, (live test).2.1, (live test).2.2.1, (live test).2.2.2.1,
      SourceCurrentAllocatedLocalReductionActual.ranges_of_finite (live test).2.2.2.2⟩)
    initial.correct initial.stored initial.covered initial.globals initial.probes
  exact ⟨⟨receipt.ready, receipt.admitted,
    initial.sound.advance formulas solver after savedFourth saved receipt.effects,
    receipt.stored, receipt.covered, receipt.correct, receipt.globals, probes⟩,
    receipt.effects, receipt.retained, receipt.fourthRetained⟩

/-- Initial caller facts and live-only inputs construct stable parent execution and its full receipt. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (initial : Context formulas solver inventory before memos)
    (live : LiveInputs budget original loaded inherited values before) :
    ∃ result after savedFourth saved next final,
      StableRun (fun g s r e p h m c n =>
        edge g s r e p h m c n budget symbol original inherited values before.checked before.fourth before.merge)
        result after savedFourth saved ∧
      ∃ actual : Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
          result after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next symbol original loaded inherited values before.checked result after
          before.fourth savedFourth before.merge saved final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  cases test : contradictory original with
  | true =>
      obtain ⟨_, _, receipt⟩ := SourceCurrentAllocatedParentEdge.rejected formulas solver inventory budget symbol
        original loaded inherited values before.checked before.fourth before.merge initial.ready initial.admitted
        test initial.correct initial.stored initial.covered memos initial.globals
      let actual : Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
          (SourceCurrentAllocatedMkEdge.reject symbol before.checked).1
          (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2 before.fourth before.merge := .rejected test
      have reads : Reads formulas solver actual memos memos := .rejected (test := test)
      exact ⟨_, _, before.fourth, before.merge, inventory, memos,
        SourceCurrentAllocatedParentWorkerCompletion.edge_complete actual (fun falseTest => (live falseTest).2.1),
        actual, reads, receipt, caller_post formulas solver reads initial live receipt⟩
  | false =>
      obtain ⟨cached, found, inheritedReady, available, ranges⟩ := live test
      obtain ⟨result, after, savedFourth, saved, next, final, actual, reads, receipt⟩ :=
        SourceCurrentAllocatedParentEdgeActual.finite formulas solver inventory budget symbol original loaded inherited
          values before.checked before.fourth before.merge initial.ready initial.admitted cached found inheritedReady
          available initial.correct initial.stored initial.covered (fun _ => ranges) memos initial.globals
      exact ⟨result, after, savedFourth, saved, next, final,
        SourceCurrentAllocatedParentWorkerCompletion.edge_complete actual (fun _ => found), actual, reads, receipt,
        caller_post formulas solver reads initial live receipt⟩

/-- A supplied success derives strict parent reads and the same complete returned caller. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget g s r e p h m c n : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated}
    {inherited : EqValue} {values : List (Value Symbol Guard)} {before : Caller width}
    {after : Checked width} {result : EdgeValue Symbol Guard} {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (live : LiveInputs budget original loaded inherited values before)
    (done : edge g s r e p h m c n budget symbol original inherited values before.checked before.fourth before.merge =
      .done result after savedFourth saved) :
    ∃ next final,
      ∃ actual : Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
          result after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next symbol original loaded inherited values before.checked result after
          before.fourth savedFourth before.merge saved final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  obtain ⟨chosen, reached, fourth, memo, next, final, ⟨G, S, R, E, P, H, M, C, N, stable⟩,
    actual, reads, receipt, post⟩ := finite formulas solver budget symbol original loaded inherited values initial live
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedParentWorkerStability.edge_done_unique
    (stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  exact ⟨next, final, actual, reads, receipt, post⟩

/-- Supplied successful bounds reconstruct the same actual raw parent graph. -/
theorem sound
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget g s r e p h m c n : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated}
    {inherited : EqValue} {values : List (Value Symbol Guard)} {before : Caller width}
    {after : Checked width} {result : EdgeValue Symbol Guard} {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (live : LiveInputs budget original loaded inherited values before)
    (done : edge g s r e p h m c n budget symbol original inherited values before.checked before.fourth before.merge =
      .done result after savedFourth saved) :
    Edge budget symbol original loaded inherited values before.checked before.fourth before.merge result after savedFourth saved := by
  obtain ⟨_, _, actual, _, _, _⟩ := verified formulas solver initial live done
  exact actual

/-- Raw rejection constructs stable execution without a field, inherited, child, or range input. -/
theorem rejected_finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue) (values : List (Value Symbol Guard))
    (initial : Context formulas solver inventory before memos) (test : contradictory original = true) :
    ∃ loaded result after savedFourth saved next final,
      StableRun (fun g s r e p h m c n =>
        edge g s r e p h m c n budget symbol original inherited values before.checked before.fourth before.merge)
        result after savedFourth saved ∧
      ∃ actual : Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
          result after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next symbol original loaded inherited values before.checked result after
          before.fourth savedFourth before.merge saved final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  let loaded : Allocated := ⟨.contradiction, original.guard⟩
  have live : LiveInputs budget original loaded inherited values before := by
    intro impossible
    rw [test] at impossible
    cases impossible
  obtain ⟨result, after, fourth, memo, next, final, stable, actual, reads, receipt, post⟩ :=
    finite formulas solver budget symbol original loaded inherited values initial live
  exact ⟨loaded, result, after, fourth, memo, next, final, stable, actual, reads, receipt, post⟩

/-- A resident original edge derives its field, child support, actual body, and immutable law. -/
theorem resident_finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : ResidentRanges budget request before) :
    ∃ result after savedFourth saved next final,
      StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
        request.value.entry.key.constraint request.inherited request.value.children
        before.checked before.fourth before.merge) result after savedFourth saved ∧
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved),
        SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  obtain ⟨cached, loaded, found⟩ := initial.ready.good.fields request.value.entry.key request.value resident
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  have live : LiveInputs budget request.value.entry.key.constraint loaded request.inherited request.value.children before :=
    fun test => ⟨cached, found, inheritedReady, available, ranges test loaded found⟩
  obtain ⟨result, after, savedFourth, saved, next, final, stable, parent, reads, receipt, post⟩ :=
    finite formulas solver budget request.value.entry.key.symbol request.value.entry.key.constraint loaded
      request.inherited request.value.children initial live
  have law : SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
    intro ambient term
    have input := InternedGuardedLanguage.edgeMeaning_all (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term
    change InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term ↔
      SourceCurrentAllocatedParentEdge.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient
        request.value.entry.key.symbol request.value.entry.key.constraint request.value.children term at input
    exact ⟨fun accepted => input.mpr ((receipt.language ambient term).1 accepted),
      fun satisfied => ((receipt.language ambient term).2 satisfied).trans input.symm⟩
  let body : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
      (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) :=
    .parent (fun _ => found) parent
  have bodyReads : SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver body memos final :=
    .parent (field := fun _ => found) reads
  refine ⟨result, after, savedFourth, saved, next, final, stable, body, bodyReads, ?_, post⟩
  exact ⟨receipt.ready, receipt.admitted, post.context.sound, receipt.effects, receipt.resident,
    receipt.stored, receipt.covered, receipt.retained, receipt.globals, receipt.correct, receipt.fourthRetained, rfl, law⟩

/-- Supplied resident success retains its same actual body, full caller, and inherited edge law. -/
theorem resident_verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget g s r e p h m c n : Nat} {request : Request}
    {before : Caller width} {after : Checked width} {result : EdgeValue Symbol Guard}
    {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : ResidentRanges budget request before)
    (done : edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge = .done result after savedFourth saved) :
    ∃ next final,
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved),
        SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  obtain ⟨chosen, reached, fourth, memo, next, final, ⟨G, S, R, E, P, H, M, C, N, stable⟩,
    actual, reads, receipt, post⟩ := resident_finite formulas solver budget request initial inheritedReady resident ranges
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedParentWorkerStability.edge_done_unique
    (stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  exact ⟨next, final, actual, reads, receipt, post⟩

end MicroCFTA.SourceCurrentAllocatedParentWorkerActual
