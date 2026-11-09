import MicroCFTA.SourceCurrentConjunctionSharedWorklistNumeric
import MicroCFTA.SourceCurrentConjunctionSharedWorkerCompletion

/-!
# Shared numeric bounds with a fixed current guard alphabet

The caller supplies its current guard inventory. The proof uses that exact
list in every resource forecast. It keeps the original tuple budget and
replays the same actual private endpoint and saved memo.

Membership in a larger guard inventory does not by itself compare the
numeric shape sums. These bounds use no such comparison. Native capacity,
total runtime and complete source enumeration remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedFixedAlphabetNumeric
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistRun (Run)
open SourceCurrentConjunctionSharedWorklistFrame (Frame)
open SourceCurrentConjunctionSharedWorklistResourceControl (grow grow_ge grow_strict grow_mono seed Profile)
open HeightOrderControlled (Path)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "measure" => SourceCurrentConjunctionSharedWorklistNumericControl.measure
local notation "uniformP" => SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel
local notation "uniformH" => SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed

private noncomputable def controlBound (alphabet : List Guard) (budget resource : Nat) : Nat :=
  HeightOrderControlled.majorant (grow alphabet) (budget + 3) (seed budget resource)

/-- The fixed caller inventory supplies the final physical and private profile. -/
noncomputable def forecast (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentConjunctionSharedWorklistNumeric.forecast alphabet budget resource

/-- The fixed caller inventory supplies the projection ceiling. -/
noncomputable def projectionFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentConjunctionSharedWorklistNumeric.projectionFuel alphabet budget resource

/-- The fixed caller inventory supplies the native reader ceiling. -/
noncomputable def readerFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentConjunctionSharedWorklistNumeric.readerFuel alphabet budget resource

/-- The final profile retains the initial resource and original budget seed. -/
theorem forecast_ge (alphabet : List Guard) (budget resource : Nat) :
    seed budget resource ≤ forecast alphabet budget resource :=
  SourceCurrentConjunctionSharedWorklistNumeric.forecast_ge alphabet budget resource

private theorem coordinates_bound (bound scalar : Nat) (before : Frame Symbol Formula bound)
    (budget : bound ≤ scalar) (profile : Profile scalar before.state) :
    ∀ index, measure bound before.credits before.state index ≤ scalar := by
  have current : SourceCurrentConjunctionSharedWorklistNumericControl.control before.state ≤ scalar :=
    Nat.max_le.mpr ⟨Nat.le_trans before.budget budget, profile.counts.queueSize⟩
  intro index
  exact Nat.le_trans
    (SourceCurrentConjunctionSharedWorklistNumericControl.measure_bound bound before.credits before.state index) current

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem run_bound (alphabet : List Guard) (bound : Nat) {p h : Nat}
    {start : WorkState} {outcome : Outcome Symbol Formula} (actual : Run p h start outcome) :
    ∀ (before : Frame Symbol Formula bound), before.state = start → ∀ scalar, bound ≤ scalar →
      SourceCurrentConjunctionSharedWorklistValues.Invariant before.state →
      SourceCurrentConjunctionSharedWorklistClosed.Invariant before.state →
      SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant before.state →
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
        before.state.storage.requirements.physical.heap →
      Profile scalar before.state →
      ∀ event final, outcome = .done event final →
        ∃ (last : Frame Symbol Formula bound) (lastScalar length : Nat),
          Path (grow alphabet) (bound + 3) (measure bound before.credits before.state) scalar
            (measure bound last.credits last.state) lastScalar length ∧
          Profile (grow alphabet lastScalar) final ∧
          ∀ P H, uniformP lastScalar ≤ P → uniformH lastScalar ≤ H → Run P H before.state (.done event final) := by
  induction actual with
  | @failed start after fault advanced =>
      intro before stateEquation scalar budget values currentClosed queued known profile event final impossible
      cases impossible
  | @drained start after advanced =>
      intro before stateEquation scalar budget values currentClosed queued known profile event final returned
      have head : step p h before.state = .done .drained after := by rw [stateEquation]; exact advanced
      obtain ⟨nextProfile, stable⟩ := SourceCurrentConjunctionSharedWorklistResourceControl.step_bound
        alphabet bound p h scalar before .drained after values currentClosed queued known profile head
      have same : after = final := (Outcome.done.inj returned).2
      refine ⟨before, scalar, 0, Path.refl (fun index _ => coordinates_bound bound scalar before budget profile index),
        same ▸ nextProfile, ?_⟩
      intro P H enoughP enoughH
      exact returned ▸ Run.drained (stable P H enoughP enoughH)
  | @more start middle outcome advanced tail ih =>
      intro before stateEquation scalar budget values currentClosed queued known profile event final returned
      have head : step p h before.state = .done .more middle := by rw [stateEquation]; exact advanced
      obtain ⟨nextProfile, stable⟩ := SourceCurrentConjunctionSharedWorklistResourceControl.step_bound
        alphabet bound p h scalar before .more middle values currentClosed queued known profile head
      obtain ⟨_, next, nextState, _, decrease⟩ :=
        SourceCurrentConjunctionSharedWorklistNumericControl.step_below bound p h before middle head
      have nextValues : SourceCurrentConjunctionSharedWorklistValues.Invariant next.state := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before.state values).2
      have nextClosed : SourceCurrentConjunctionSharedWorklistClosed.Invariant next.state := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistClosed.step_closed p h before.state values currentClosed
      have nextQueued : SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant next.state := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistQueuedHandles.step_preserves p h before.state queued
      have nextKnown : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
          next.state.storage.requirements.physical.heap := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistAnnotations.step_heap (fun guard => guard ∈ alphabet)
            p h before.state values currentClosed known
      have nextBound : Profile (grow alphabet scalar) next.state := by
        rw [nextState]
        exact nextProfile
      obtain ⟨last, lastScalar, length, path, finalProfile, replay⟩ :=
        ih next nextState (grow alphabet scalar) (Nat.le_trans budget (grow_ge alphabet scalar))
          nextValues nextClosed nextQueued nextKnown nextBound event final returned
      have elapsed := path.elapsed_le
      have current := grow_ge alphabet scalar
      have increase : scalar ≤ lastScalar := by omega
      refine ⟨last, lastScalar, length + 1,
        Path.step (fun index _ => coordinates_bound bound scalar before budget profile index) decrease
          (grow_strict alphabet scalar) (Nat.le_refl _) path, finalProfile, ?_⟩
      intro P H enoughP enoughH
      have first := stable P H
        (Nat.le_trans (SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel_mono increase) enoughP)
        (Nat.le_trans (SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel_mono increase) enoughH)
      have remaining := replay P H enoughP enoughH
      rw [nextState] at remaining
      exact Run.more first remaining

private theorem run_unique {p h : Nat} {before : WorkState}
    {first second : Outcome Symbol Formula} (one : Run p h before first)
    (two : Run p h before second) : first = second := by
  induction one generalizing second with
  | failed actual =>
      cases two with
      | failed other => exact actual.symm.trans other
      | drained other => cases actual.symm.trans other
      | more other tail => cases actual.symm.trans other
  | drained actual =>
      cases two with
      | failed other => cases actual.symm.trans other
      | drained other => exact actual.symm.trans other
      | more other tail => cases actual.symm.trans other
  | more actual tail ih =>
      cases two with
      | failed other => cases actual.symm.trans other
      | drained other => cases actual.symm.trans other
      | more other rest =>
          have same := Outcome.done.inj (actual.symm.trans other)
          cases same.2
          exact ih rest

/-- Current facts and the fixed guard inventory derive the same drained endpoint above computed ceilings. -/
theorem explore_bound (alphabet : List Guard) (budget : Nat) (start : Node) (before : Physical) (resource : Nat)
    (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    ∃ after,
      (∀ P H, projectionFuel alphabet budget resource ≤ P →
        readerFuel alphabet budget resource ≤ H →
        SourceCurrentConjunctionSharedWorklistRun.explore P H budget start before = .done .drained after) ∧
      Profile (forecast alphabet budget resource) after := by
  obtain ⟨p, h, after, stable⟩ :=
    SourceCurrentConjunctionSharedWorklistCompletion.explore_initial budget start before ready available
  have completed := stable p h (Nat.le_refl _) (Nat.le_refl _)
  have trace := SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before
  rw [completed] at trace
  have initialProfile := SourceCurrentConjunctionSharedWorklistResourceControl.initial_profile
    budget start before resource fits
  have budgetBound : budget ≤ seed budget resource :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  obtain ⟨last, lastScalar, length, path, finalProfile, replay⟩ := run_bound alphabet budget trace
    (SourceCurrentConjunctionSharedWorklistFrame.initial budget start before) rfl (seed budget resource) budgetBound
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
    (SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget start before)
    (SourceCurrentConjunctionSharedWorklistQueuedHandles.initial budget start before)
    known initialProfile .drained after rfl
  have bound : lastScalar ≤ controlBound alphabet budget resource :=
    path.final_le (grow_mono alphabet) (grow_strict alphabet)
  refine ⟨after, ?_, finalProfile.mono (grow_mono alphabet bound)⟩
  intro P H enoughP enoughH
  have observed := replay P H
    (Nat.le_trans (SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel_mono bound) enoughP)
    (Nat.le_trans (SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel_mono bound) enoughH)
  exact (run_unique observed (SourceCurrentConjunctionSharedWorklistRun.explore_graph P H budget start before)).symm

variable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- The fixed current guard inventory derives the same complete decision above computed ceilings. -/
theorem decision_bound (alphabet : List Guard) (budget : Nat) (start : Node) (before : Physical) (resource : Nat)
    (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    ∃ answer after,
      (∀ P H, projectionFuel alphabet budget resource ≤ P →
        readerFuel alphabet budget resource ≤ H →
        SourceCurrentConjunctionSharedWorker.decision P H budget start before = .done answer after) ∧
      Profile (forecast alphabet budget resource) after := by
  cases classified : closed start with
  | false =>
      refine ⟨false, SourceCurrentConjunctionSharedWorklistStep.initial budget start before, ?_, ?_⟩
      · intro P H _ _
        exact SourceCurrentConjunctionSharedWorker.decision_open P H budget start before classified
      · exact (SourceCurrentConjunctionSharedWorklistResourceControl.initial_profile
          budget start before resource fits).mono (forecast_ge _ budget resource)
  | true =>
      obtain ⟨after, stable, profile⟩ :=
        explore_bound alphabet budget start before resource ready available fits known
      let p := projectionFuel alphabet budget resource
      let h := readerFuel alphabet budget resource
      have explored := stable p h (Nat.le_refl _) (Nat.le_refl _)
      obtain ⟨table, read⟩ :=
        SourceCurrentConjunctionSharedWorker.endpoint_materializable p h budget start before after explored
      have grown := SourceCurrentConjunctionEmptinessTable.grow_rounds_complete .empty key closed
        table table.length 0 (by omega)
      have actual := SourceCurrentConjunctionSharedWorker.decision_closed_done p h budget start before after
        table _ classified explored read grown
      let known := ConservativeEmptiness.possible
        (SourceCurrentConjunctionEmptinessTable.states key table)
        (SourceCurrentConjunctionEmptinessTable.rows .empty key closed table)
      let answer := SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start
      refine ⟨answer, after, ?_, profile⟩
      intro P H enoughP enoughH
      exact SourceCurrentConjunctionSharedWorkerStability.decision_done_stable actual enoughP enoughH

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Current inputs derive the same complete call, private snapshot and saved memo above computed bounds. -/
theorem call_bound [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (alphabet : List ConcreteGuard) (budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before : ConcretePhysical) (resource : Nat) (ready : Ready before)
    (available : Available before.heap query) (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    ∃ answer saved after,
      (∀ P H, projectionFuel alphabet budget resource ≤ P →
        readerFuel alphabet budget resource ≤ H →
        SourceCurrentConjunctionSharedWorker.call P H budget memo query before = .done (answer, saved) after) ∧
      Profile (forecast alphabet budget resource) after := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, answer⟩ := entry
      refine ⟨answer, memo, SourceCurrentConjunctionSharedWorklistStep.initial budget query before, ?_, ?_⟩
      · intro P H _ _
        exact SourceCurrentConjunctionSharedWorker.call_hit P H budget memo query original before answer found
      · exact (SourceCurrentConjunctionSharedWorklistResourceControl.initial_profile
          budget query before resource fits).mono (forecast_ge _ budget resource)
  | none =>
      obtain ⟨answer, after, stable, profile⟩ := decision_bound alphabet budget query before resource ready available fits known
      refine ⟨answer, SourceCurrentEmptinessMemo.insert memo query answer, after, ?_, profile⟩
      intro P H enoughP enoughH
      exact SourceCurrentConjunctionSharedWorker.call_done P H budget memo query before after answer found
        (stable P H enoughP enoughH)


end MicroCFTA.SourceCurrentConjunctionSharedFixedAlphabetNumeric
