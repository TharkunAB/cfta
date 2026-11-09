import MicroCFTA.SourceCurrentConjunctionSharedWorklistCountBounds
import MicroCFTA.SourceCurrentConjunctionSharedWorklistWidthBounds
import MicroCFTA.SourceCurrentConjunctionSharedWorklistStepNumericBounds
import MicroCFTA.SourceCurrentConjunctionSharedWorklistStepNumeric
import MicroCFTA.SourceCurrentConjunctionSharedWorklistStability

/-!
# Numeric growth of the actual shared worklist

One current scalar bounds the native heap and every private dimension used
by the next step. The fixed guard alphabet bounds new row descriptors.
Actual successful steps derive their own next profile and exact replay.
The growth function is strict and monotone. No future profile is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistResourceControl
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistFrame (Frame)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRequirementRowsNumericControl (freshSize)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula

/-- The native forecast and new row dimensions determine one strict scalar step. -/
noncomputable def grow (alphabet : List Guard) (scalar : Nat) : Nat :=
  1 + max (SourceCurrentConjunctionSharedWorklistStepNumericBounds.forecast scalar)
    (2 * scalar + shapeThrough alphabet scalar + freshSize alphabet scalar scalar + 2)

/-- Every growth step retains the current scalar. -/
theorem grow_ge (alphabet : List Guard) (scalar : Nat) : scalar ≤ grow alphabet scalar := by
  have enough := SourceCurrentConjunctionSharedWorklistStepNumericBounds.forecast_ge scalar
  unfold grow
  omega

/-- A strict scalar step pays for one continuing transition. -/
theorem grow_strict (alphabet : List Guard) (scalar : Nat) : scalar < grow alphabet scalar := by
  have enough := SourceCurrentConjunctionSharedWorklistStepNumericBounds.forecast_ge scalar
  unfold grow
  omega

/-- Larger current limits retain every earlier complete step forecast. -/
theorem grow_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) :
    grow alphabet first ≤ grow alphabet last := by
  have native := SourceCurrentConjunctionSharedWorklistStepNumericBounds.forecast_mono increase
  have shapes := SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet increase
  have fresh := SourceCurrentConjunctionRequirementRowsNumericControl.freshSize_mono alphabet increase increase
  have rows : 2 * first + shapeThrough alphabet first + freshSize alphabet first first + 2 ≤
      2 * last + shapeThrough alphabet last + freshSize alphabet last last + 2 := by omega
  unfold grow
  apply Nat.add_le_add_left
  exact Nat.max_le.mpr ⟨Nat.le_trans native (Nat.le_max_left _ _),
    Nat.le_trans rows (Nat.le_max_right _ _)⟩

/-- The current native heap, private counts and operand widths share one scalar. -/
structure Profile (scalar : Nat) (before : WorkState) : Prop where
  fits : Fits scalar before.storage.requirements.physical.heap
  counts : SourceCurrentConjunctionSharedWorklistCountBounds.Counts scalar before
  widths : SourceCurrentConjunctionSharedWorklistWidthBounds.Widths scalar before

/-- A larger scalar retains the complete current quantitative profile. -/
theorem Profile.mono {first last : Nat} {before : WorkState} (prior : Profile first before)
    (increase : first ≤ last) : Profile last before :=
  ⟨prior.fits.mono increase, prior.counts.mono increase, prior.widths.mono increase⟩

/-- The original heap scalar, tuple budget and one initial operand fix the seed. -/
def seed (budget resource : Nat) : Nat := max resource (max budget 1)

/-- Original initialization derives its complete quantitative profile. -/
theorem initial_profile (budget : Nat) (start : Node) (before : Physical) (resource : Nat)
    (fits : Fits resource before.heap) : Profile (seed budget resource) (initial budget start before) := by
  have one : 1 ≤ seed budget resource := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have counts := SourceCurrentConjunctionSharedWorklistCountBounds.initial_counts budget start before
  refine ⟨fits.mono (Nat.le_max_left _ _), ?_,
    (SourceCurrentConjunctionSharedWorklistWidthBounds.initial_widths budget start before).mono one⟩
  exact ⟨Nat.le_trans counts.cellCount one, Nat.le_trans counts.stateSize one,
    Nat.le_trans counts.cachedSize one, Nat.le_trans counts.queueSize one,
    Nat.le_trans counts.tableCount one⟩

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem scheduled_step (bound p h scalar : Nat) (before : Frame Symbol Formula bound)
    (event : Event) (after : WorkState)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before.state)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before.state)
    (queued : SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant before.state)
    (profile : Profile scalar before.state) (actual : step p h before.state = .done event after) :
    (∀ P H, SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel scalar ≤ P →
      SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel scalar ≤ H →
      step P H before.state = .done event after) ∧
    Fits (SourceCurrentConjunctionSharedWorklistStepNumericBounds.forecast scalar)
      after.storage.requirements.physical.heap := by
  obtain ⟨foundEvent, foundAfter, stable, finalFits⟩ :=
    SourceCurrentConjunctionSharedWorklistStepNumeric.complete bound before scalar values closed queued profile.fits
  let p0 := SourceCurrentConjunctionSharedWorklistStepNumeric.projectionFuel before.state
  let h0 := SourceCurrentConjunctionSharedWorklistStepNumeric.readerFuel before.state scalar
  have first := SourceCurrentConjunctionSharedWorklistStability.step_done_stable actual
    (Nat.le_max_left p p0) (Nat.le_max_left h h0)
  have second := stable (max p p0) (max h h0) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have same := Outcome.done.inj (first.symm.trans second)
  cases same.1
  cases same.2
  have limits := SourceCurrentConjunctionSharedWorklistStepNumericBounds.bounds before.state scalar scalar
    (Nat.le_refl _) profile.widths.pending profile.counts.stateSize
  refine ⟨fun P H enoughP enoughH => stable P H
    (Nat.le_trans limits.2.1 enoughP) (Nat.le_trans limits.2.2 enoughH), finalFits.mono limits.1⟩

/-- An actual step derives its next profile and its exact complete replay at uniform scalar ceilings. -/
theorem step_bound (alphabet : List Guard) (bound p h scalar : Nat) (before : Frame Symbol Formula bound)
    (event : Event) (after : WorkState)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before.state)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before.state)
    (queued : SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant before.state)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
      before.state.storage.requirements.physical.heap)
    (profile : Profile scalar before.state) (actual : step p h before.state = .done event after) :
    Profile (grow alphabet scalar) after ∧
      ∀ P H, SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel scalar ≤ P →
        SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel scalar ≤ H →
        step P H before.state = .done event after := by
  obtain ⟨stable, finalFits⟩ := scheduled_step bound p h scalar before event after values closed queued profile actual
  obtain ⟨cells, sizes, cached, queue, table⟩ :=
    SourceCurrentConjunctionSharedWorklistCountBounds.step_bounds alphabet scalar p h before.state event after
      values profile.widths.raw known profile.fits profile.counts actual
  have nextWidths := SourceCurrentConjunctionSharedWorklistWidthBounds.step_widths scalar p h before.state profile.widths
  have widths : SourceCurrentConjunctionSharedWorklistWidthBounds.Widths
      (max scalar (SourceCurrentConjunctionRequirementCellsSize.stateSize before.state.storage.requirements)) after := by
    simpa only [actual, Outcome.state] using nextWidths
  have native : SourceCurrentConjunctionSharedWorklistStepNumericBounds.forecast scalar ≤ grow alphabet scalar := by
    unfold grow
    omega
  have rows : 2 * scalar + shapeThrough alphabet scalar + freshSize alphabet scalar scalar + 2 ≤
      grow alphabet scalar := by
    unfold grow
    omega
  have current := grow_ge alphabet scalar
  have fresh : freshSize alphabet scalar scalar ≤ grow alphabet scalar := by omega
  have wider : max scalar (SourceCurrentConjunctionRequirementCellsSize.stateSize before.state.storage.requirements) ≤
      grow alphabet scalar := Nat.max_le.mpr ⟨current, Nat.le_trans profile.counts.stateSize current⟩
  refine ⟨⟨finalFits.mono native, ?_, widths.mono wider⟩, stable⟩
  exact ⟨by omega, Nat.le_trans sizes (Nat.max_le.mpr ⟨current, fresh⟩), by omega, by omega, by omega⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistResourceControl
