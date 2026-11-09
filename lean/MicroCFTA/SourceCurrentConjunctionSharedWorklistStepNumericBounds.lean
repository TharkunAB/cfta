import MicroCFTA.SourceCurrentConjunctionSharedWorklistStepNumeric
import MicroCFTA.SourceCurrentConjunctionRequirementCellsSize

/-!
# Uniform bounds for the current shared transition schedule

One current scalar bounds the heap resource, queued operand widths, and
stored cell size. These data bound the exact existing transition schedule.
The bounds need no readiness, completed transition, or future profile.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistStepNumericBounds
open InternedConstructorTemplates (Value)
open SourceCurrentConjunctionSharedWorklistStep (Task)
open SourceCurrentConjunctionProjectionResources (jobsBound workerFuel)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- The scalar bounds one complete cell force and the following operand sample. -/
def forecast (scalar : Nat) : Nat :=
  SourceCurrentConjunctionExposureResources.forecast scalar (jobsBound scalar scalar scalar scalar)

/-- The scalar bounds the longest pending projection path. -/
def projectionFuel (scalar : Nat) : Nat := workerFuel scalar

/-- The final scalar schedule bounds both forcing and sampling reads. -/
def readerFuel (scalar : Nat) : Nat :=
  SourceCurrentProjectionUnionResources.readFuel (forecast scalar)

/-- The uniform forecast retains its original scalar. -/
theorem forecast_ge (scalar : Nat) : scalar ≤ forecast scalar :=
  Nat.le_trans (SourceCurrentConjunctionProjectionResources.jobsBound_ge scalar scalar scalar scalar)
    (SourceCurrentConjunctionExposureResources.forecast_ge scalar _)

/-- Larger current scalars retain the entire uniform forecast. -/
theorem forecast_mono {first last : Nat} (increase : first ≤ last) : forecast first ≤ forecast last := by
  have limits := SourceCurrentConjunctionProjectionResources.jobsBound_limits_mono increase increase first first
  have count := SourceCurrentConjunctionProjectionResources.jobsBound_count_mono last last increase first
  have resource := SourceCurrentConjunctionProjectionResources.jobsBound_mono last last last increase
  exact SourceCurrentConjunctionExposureResources.forecast_mono increase
    (Nat.le_trans limits (Nat.le_trans count resource))

/-- Larger current scalars retain the projection worker ceiling. -/
theorem projectionFuel_mono {first last : Nat} (increase : first ≤ last) :
    projectionFuel first ≤ projectionFuel last :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 2 increase) 1

/-- Larger current scalars retain the recursive reader ceiling. -/
theorem readerFuel_mono {first last : Nat} (increase : first ≤ last) :
    readerFuel first ≤ readerFuel last :=
  SourceCurrentProjectionUnionResources.readFuel_mono (forecast_mono increase)

private theorem cell_limits (handle : Nat) (before : Cells) (scalar : Nat)
    (bounded : SourceCurrentConjunctionRequirementCellsSize.stateSize before ≤ scalar) :
    SourceCurrentConjunctionRequirementCellsNumeric.depth
        (SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs handle before) ≤ scalar ∧
      SourceCurrentConjunctionRequirementCellsNumeric.width
        (SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs handle before) ≤ scalar ∧
      (SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs handle before).length ≤ scalar ∧
      SourceCurrentConjunctionRequirementCellsOutputBounds.bound handle before ≤ scalar := by
  cases found : SourceCurrentConjunctionRequirementCells.lookup handle before with
  | none =>
      simp only [SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs, found,
        SourceCurrentConjunctionRequirementCellsNumeric.depth,
        SourceCurrentConjunctionRequirementCellsNumeric.width, List.foldr_nil, List.length_nil,
        SourceCurrentConjunctionRequirementCellsOutputBounds.bound]
      exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  | some cell =>
      have known := Nat.le_trans
        (SourceCurrentConjunctionRequirementCellsSize.lookup_size handle before cell found) bounded
      cases cell with
      | column nodes =>
          simp only [SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs, found,
            SourceCurrentConjunctionRequirementCellsNumeric.depth,
            SourceCurrentConjunctionRequirementCellsNumeric.width, List.foldr_nil, List.length_nil,
            SourceCurrentConjunctionRequirementCellsOutputBounds.bound]
          exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, known⟩
      | done nodes =>
          simp only [SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs, found,
            SourceCurrentConjunctionRequirementCellsNumeric.depth,
            SourceCurrentConjunctionRequirementCellsNumeric.width, List.foldr_nil, List.length_nil,
            SourceCurrentConjunctionRequirementCellsOutputBounds.bound]
          exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, known⟩
      | pending cursor =>
          change max (SourceCurrentConjunctionRequirementCellsNumeric.depth cursor.pending)
            (max (SourceCurrentConjunctionRequirementCellsNumeric.width cursor.pending)
              (cursor.collected.length + cursor.pending.length)) ≤ scalar at known
          have depth := Nat.le_trans (Nat.le_max_left _ _) known
          have width := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) known
          have count := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) known
          simp only [SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs, found,
            SourceCurrentConjunctionRequirementCellsOutputBounds.bound]
          exact ⟨depth, width, by omega, count⟩

private theorem cell_forecast_le (handle : Nat) (before : Cells) (resource scalar : Nat)
    (resources : resource ≤ scalar)
    (bounded : SourceCurrentConjunctionRequirementCellsSize.stateSize before ≤ scalar) :
    SourceCurrentConjunctionRequirementCellsNumeric.forecast handle before resource ≤
      jobsBound scalar scalar scalar scalar := by
  have limits := cell_limits handle before scalar bounded
  have dimensions := SourceCurrentConjunctionProjectionResources.jobsBound_limits_mono limits.1 limits.2.1
    (SourceCurrentConjunctionRequirementCellsNumeric.pendingJobs handle before).length resource
  have count := SourceCurrentConjunctionProjectionResources.jobsBound_count_mono scalar scalar limits.2.2.1 resource
  have amounts := SourceCurrentConjunctionProjectionResources.jobsBound_mono scalar scalar scalar resources
  exact Nat.le_trans dimensions (Nat.le_trans count amounts)

/-- Current widths and cell size bound all three exact transition schedules. -/
theorem bounds (before : WorkState) (resource scalar : Nat) (resources : resource ≤ scalar)
    (nodeWidths : ∀ nodes : List Node, Task.nodes nodes ∈ before.pending → nodes.length ≤ scalar)
    (cellSize : SourceCurrentConjunctionRequirementCellsSize.stateSize before.storage.requirements ≤ scalar) :
    SourceCurrentConjunctionSharedWorklistStepNumeric.forecast before resource ≤ forecast scalar ∧
      SourceCurrentConjunctionSharedWorklistStepNumeric.projectionFuel before ≤ projectionFuel scalar ∧
      SourceCurrentConjunctionSharedWorklistStepNumeric.readerFuel before resource ≤ readerFuel scalar := by
  have pure : resource ≤ forecast scalar ∧ 0 ≤ projectionFuel scalar ∧ 0 ≤ readerFuel scalar :=
    ⟨Nat.le_trans resources (forecast_ge scalar), Nat.zero_le _, Nat.zero_le _⟩
  cases pending : before.pending with
  | nil =>
      simpa only [SourceCurrentConjunctionSharedWorklistStepNumeric.forecast,
        SourceCurrentConjunctionSharedWorklistStepNumeric.projectionFuel,
        SourceCurrentConjunctionSharedWorklistStepNumeric.readerFuel, pending] using pure
  | cons task rest =>
      cases task with
      | nodes nodes =>
          have width := nodeWidths nodes (by rw [pending]; exact List.mem_cons_self)
          have amount := Nat.le_trans resources
            (SourceCurrentConjunctionProjectionResources.jobsBound_ge scalar scalar scalar scalar)
          have sampled : SourceCurrentConjunctionExposureResources.forecast nodes.length resource ≤ forecast scalar :=
            SourceCurrentConjunctionExposureResources.forecast_mono width amount
          simp only [SourceCurrentConjunctionSharedWorklistStepNumeric.forecast,
            SourceCurrentConjunctionSharedWorklistStepNumeric.projectionFuel,
            SourceCurrentConjunctionSharedWorklistStepNumeric.readerFuel, pending]
          exact ⟨sampled, Nat.zero_le _, SourceCurrentProjectionUnionResources.readFuel_mono sampled⟩
      | requirements handles =>
          cases handles with
          | nil =>
              simpa only [SourceCurrentConjunctionSharedWorklistStepNumeric.forecast,
                SourceCurrentConjunctionSharedWorklistStepNumeric.projectionFuel,
                SourceCurrentConjunctionSharedWorklistStepNumeric.readerFuel, pending] using pure
          | cons handle handles =>
              have limits := cell_limits handle before.storage.requirements scalar cellSize
              have first := cell_forecast_le handle before.storage.requirements resource scalar resources cellSize
              have sampled : SourceCurrentConjunctionExposureResources.forecast
                  (SourceCurrentConjunctionRequirementCellsOutputBounds.bound handle before.storage.requirements)
                  (SourceCurrentConjunctionRequirementCellsNumeric.forecast handle before.storage.requirements resource) ≤
                    forecast scalar :=
                SourceCurrentConjunctionExposureResources.forecast_mono limits.2.2.2 first
              have forcedRead : SourceCurrentConjunctionRequirementCellsNumeric.readerFuel
                  handle before.storage.requirements resource ≤ readerFuel scalar :=
                SourceCurrentProjectionUnionResources.readFuel_mono (Nat.le_trans first
                  (SourceCurrentConjunctionExposureResources.forecast_ge scalar _))
              have sampledRead : SourceCurrentConjunctionTuplePullNumeric.fuel
                  (SourceCurrentConjunctionRequirementCellsOutputBounds.bound handle before.storage.requirements)
                  (SourceCurrentConjunctionRequirementCellsNumeric.forecast handle before.storage.requirements resource) ≤
                    readerFuel scalar :=
                SourceCurrentProjectionUnionResources.readFuel_mono sampled
              have projection : SourceCurrentConjunctionRequirementCellsNumeric.projectionFuel
                  handle before.storage.requirements ≤ projectionFuel scalar :=
                Nat.add_le_add_right (Nat.mul_le_mul_left 2 limits.1) 1
              simp only [SourceCurrentConjunctionSharedWorklistStepNumeric.forecast,
                SourceCurrentConjunctionSharedWorklistStepNumeric.projectionFuel,
                SourceCurrentConjunctionSharedWorklistStepNumeric.readerFuel, pending]
              exact ⟨sampled, projection, Nat.max_le.mpr ⟨forcedRead, sampledRead⟩⟩
      | rows handle =>
          simpa only [SourceCurrentConjunctionSharedWorklistStepNumeric.forecast,
            SourceCurrentConjunctionSharedWorklistStepNumeric.projectionFuel,
            SourceCurrentConjunctionSharedWorklistStepNumeric.readerFuel, pending] using pure

end MicroCFTA.SourceCurrentConjunctionSharedWorklistStepNumericBounds
