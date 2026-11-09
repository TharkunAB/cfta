import MicroCFTA.SourceCurrentConjunctionSharedWorkerNumeric
import MicroCFTA.HeightOrderControlledMonotone

/-!
# Monotone shared schedules at a fixed guard alphabet

Larger budgets increase the finite rank dimension and initial seed.
Larger heap resources increase the same seed. The existing controlled
majorant therefore bounds all three actual schedules monotonically.
The guard alphabet stays fixed throughout each comparison.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedNumericMonotone
open SourceCurrentConjunctionSharedWorklistResourceControl (seed grow grow_mono grow_strict)
variable {Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Larger budgets and resources retain the original initialized scalar. -/
theorem seed_mono {firstBudget lastBudget firstResource lastResource : Nat}
    (budgets : firstBudget ≤ lastBudget) (resources : firstResource ≤ lastResource) :
    seed firstBudget firstResource ≤ seed lastBudget lastResource := by
  unfold seed
  refine Nat.max_le.mpr ⟨Nat.le_trans resources (Nat.le_max_left _ _), ?_⟩
  exact Nat.max_le.mpr
    ⟨Nat.le_trans budgets (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩

/-- The exact controlled majorant increases with both original inputs. -/
theorem control_mono (alphabet : List Guard)
    {firstBudget lastBudget firstResource lastResource : Nat}
    (budgets : firstBudget ≤ lastBudget) (resources : firstResource ≤ lastResource) :
    HeightOrderControlled.majorant (grow alphabet) (firstBudget + 3) (seed firstBudget firstResource) ≤
      HeightOrderControlled.majorant (grow alphabet) (lastBudget + 3) (seed lastBudget lastResource) :=
  HeightOrderControlled.majorant_joint_mono (grow alphabet) (grow_mono alphabet) (grow_strict alphabet)
    (Nat.add_le_add_right budgets 3) (seed_mono budgets resources)

/-- The actual shared forecast increases with budget and resource at the same alphabet. -/
theorem forecast_mono (alphabet : List Guard)
    {firstBudget lastBudget firstResource lastResource : Nat}
    (budgets : firstBudget ≤ lastBudget) (resources : firstResource ≤ lastResource) :
    SourceCurrentConjunctionSharedWorkerNumeric.forecast alphabet firstBudget firstResource ≤
      SourceCurrentConjunctionSharedWorkerNumeric.forecast alphabet lastBudget lastResource := by
  change grow alphabet
      (HeightOrderControlled.majorant (grow alphabet) (firstBudget + 3) (seed firstBudget firstResource)) ≤
    grow alphabet
      (HeightOrderControlled.majorant (grow alphabet) (lastBudget + 3) (seed lastBudget lastResource))
  exact grow_mono alphabet (control_mono alphabet budgets resources)

/-- The actual shared projection ceiling increases with both original inputs. -/
theorem projectionFuel_mono (alphabet : List Guard)
    {firstBudget lastBudget firstResource lastResource : Nat}
    (budgets : firstBudget ≤ lastBudget) (resources : firstResource ≤ lastResource) :
    SourceCurrentConjunctionSharedWorkerNumeric.projectionFuel alphabet firstBudget firstResource ≤
      SourceCurrentConjunctionSharedWorkerNumeric.projectionFuel alphabet lastBudget lastResource := by
  change SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel
      (HeightOrderControlled.majorant (grow alphabet) (firstBudget + 3) (seed firstBudget firstResource)) ≤
    SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel
      (HeightOrderControlled.majorant (grow alphabet) (lastBudget + 3) (seed lastBudget lastResource))
  exact SourceCurrentConjunctionSharedWorklistStepNumericBounds.projectionFuel_mono
    (control_mono alphabet budgets resources)

/-- The actual shared reader ceiling increases with both original inputs. -/
theorem readerFuel_mono (alphabet : List Guard)
    {firstBudget lastBudget firstResource lastResource : Nat}
    (budgets : firstBudget ≤ lastBudget) (resources : firstResource ≤ lastResource) :
    SourceCurrentConjunctionSharedWorkerNumeric.readerFuel alphabet firstBudget firstResource ≤
      SourceCurrentConjunctionSharedWorkerNumeric.readerFuel alphabet lastBudget lastResource := by
  change SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel
      (HeightOrderControlled.majorant (grow alphabet) (firstBudget + 3) (seed firstBudget firstResource)) ≤
    SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel
      (HeightOrderControlled.majorant (grow alphabet) (lastBudget + 3) (seed lastBudget lastResource))
  exact SourceCurrentConjunctionSharedWorklistStepNumericBounds.readerFuel_mono
    (control_mono alphabet budgets resources)

end MicroCFTA.SourceCurrentConjunctionSharedNumericMonotone
