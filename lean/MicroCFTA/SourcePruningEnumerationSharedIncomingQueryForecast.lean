import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryResources

/-!
# Complete native credit in the shared incoming forecast

The shared forecast bounds the complete native step that precedes it.
The shared phase retains the native step's domain counter. These component
bounds support an ordered reservation at the actual warm query entry.
No comparison between different guard inventories is used.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
open SourceCurrentAllocatedNativeResourceForecast (Profile Le step)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "alphabetAfter" => SourceCurrentGeneratedQueryGuardResources.forecast
local notation "budget" => SourceCurrentConjunctionTupleBudget.currentTupleBudget
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound

/-- The combined shared forecast bounds the complete preceding native query step. -/
theorem native_step_le_forecast (alphabet : List Guard) (profile : Profile) :
    Le (step profile) (forecast alphabet profile) := by
  have bound : scalar (step profile) ≤
      SourceCurrentConjunctionSharedFixedAlphabetNumeric.forecast
        (alphabetAfter alphabet profile) budget (scalar (step profile)) :=
    Nat.le_trans (Nat.le_max_left _ _)
      (SourceCurrentConjunctionSharedFixedAlphabetNumeric.forecast_ge _ _ _)
  change (step profile).nodes ≤ _ ∧ (step profile).edges ≤ _ ∧ (step profile).domains ≤ _ ∧
    (step profile).mass ≤ _
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes _) bound,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges _) bound, Nat.le_refl _,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass _) bound⟩

/-- The shared phase keeps the warm domains and the native query's instruction reservation. -/
theorem forecast_domains (alphabet : List Guard) (profile : Profile) :
    (forecast alphabet profile).domains =
      profile.domains + instructionBound profile.nodes profile.edges profile.mass := rfl

end MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
