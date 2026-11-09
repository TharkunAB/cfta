import MicroCFTA.SourceCurrentConjunctionSharedWorklistResourceControl
import MicroCFTA.SourceCurrentConjunctionSharedWorklistCompletion
import MicroCFTA.SourceCurrentConjunctionSharedWorklistAnnotations
import MicroCFTA.SourceCurrentConjunctionGuardUniverse

/-!
# Initial numeric ceilings for actual shared exploration

The original heap supplies its finite guard alphabet. The original budget
fixes the rank dimension. A controlled path through the actual successful
execution bounds every later scalar from the initial profile alone.

Local replay uses these computed scalars. It does not require the computed
ceilings to exceed the earlier existential observation bounds. The result
retains the same private endpoint and its final resource profile. It does
not bound total native runtime or select a different checked caller.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistNumeric
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

private noncomputable def controlBound (alphabet : List Guard) (budget resource : Nat) : Nat :=
  HeightOrderControlled.majorant (grow alphabet) (budget + 3) (seed budget resource)

/-- The final profile includes the terminal transition after the controlled path. -/
noncomputable def forecast (alphabet : List Guard) (budget resource : Nat) : Nat :=
  grow alphabet (controlBound alphabet budget resource)

/-- The controlled path supplies one initial projection ceiling for every transition. -/
noncomputable def projectionFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  uniformP (controlBound alphabet budget resource)

/-- The controlled path supplies one initial reader ceiling for every transition. -/
noncomputable def readerFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  uniformH (controlBound alphabet budget resource)

/-- The final forecast retains the entire initial seed, including budget and private counts. -/
theorem forecast_ge (alphabet : List Guard) (budget resource : Nat) :
    seed budget resource ≤ forecast alphabet budget resource := by
  exact Nat.le_trans
    (HeightOrderControlled.majorant_ge (grow alphabet) (grow_strict alphabet) (budget + 3) (seed budget resource))
    (grow_ge alphabet _)

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
      intro before stateEquation scalar budget values closed queued known profile event final impossible
      cases impossible
  | @drained start after advanced =>
      intro before stateEquation scalar budget values closed queued known profile event final returned
      have head : step p h before.state = .done .drained after := by rw [stateEquation]; exact advanced
      obtain ⟨nextProfile, stable⟩ := SourceCurrentConjunctionSharedWorklistResourceControl.step_bound
        alphabet bound p h scalar before .drained after values closed queued known profile head
      have same : after = final := (Outcome.done.inj returned).2
      refine ⟨before, scalar, 0, Path.refl (fun index _ => coordinates_bound bound scalar before budget profile index),
        same ▸ nextProfile, ?_⟩
      intro P H enoughP enoughH
      exact returned ▸ Run.drained (stable P H enoughP enoughH)
  | @more start middle outcome advanced tail ih =>
      intro before stateEquation scalar budget values closed queued known profile event final returned
      have head : step p h before.state = .done .more middle := by rw [stateEquation]; exact advanced
      obtain ⟨nextProfile, stable⟩ := SourceCurrentConjunctionSharedWorklistResourceControl.step_bound
        alphabet bound p h scalar before .more middle values closed queued known profile head
      obtain ⟨_, next, nextState, _, decrease⟩ :=
        SourceCurrentConjunctionSharedWorklistNumericControl.step_below bound p h before middle head
      have nextValues : SourceCurrentConjunctionSharedWorklistValues.Invariant next.state := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before.state values).2
      have nextClosed : SourceCurrentConjunctionSharedWorklistClosed.Invariant next.state := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistClosed.step_closed p h before.state values closed
      have nextQueued : SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant next.state := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistQueuedHandles.step_preserves p h before.state queued
      have nextKnown : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
          next.state.storage.requirements.physical.heap := by
        rw [nextState]
        simpa only [head, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistAnnotations.step_heap (fun guard => guard ∈ alphabet)
            p h before.state values closed known
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

/-- Current initial facts derive one exact drained endpoint at the computed ceilings and every larger pair. -/
theorem explore_initial (budget : Nat) (start : Node) (before : Physical) (resource : Nat)
    (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap) :
    ∃ after,
      (∀ P H, projectionFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ P →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ H →
        SourceCurrentConjunctionSharedWorklistRun.explore P H budget start before = .done .drained after) ∧
      Profile (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource) after := by
  let alphabet := SourceCurrentConjunctionGuardUniverse.guards before.heap
  obtain ⟨p, h, after, stable⟩ :=
    SourceCurrentConjunctionSharedWorklistCompletion.explore_initial budget start before ready available
  have completed := stable p h (Nat.le_refl _) (Nat.le_refl _)
  have trace := SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before
  rw [completed] at trace
  have initialProfile := SourceCurrentConjunctionSharedWorklistResourceControl.initial_profile
    budget start before resource fits
  have known := SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts
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

end MicroCFTA.SourceCurrentConjunctionSharedWorklistNumeric
