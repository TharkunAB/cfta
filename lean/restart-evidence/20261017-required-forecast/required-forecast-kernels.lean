import MicroCFTA.SourceCurrentConstrainedCapRequiredForecast

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.RequiredForecastIntegration
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
namespace Forecast
export SourceCurrentConstrainedCapRequiredForecast
  (scalar stageProfile headProfile constructorProfile planProfile rowStep scan
   stage_head_profile stage_constructor_profile plan_stage plan_child_return
   plan_row_return plan_level_mono plan_mono)
end Forecast

/-- One final reservation covers the actual open Head and a scheduled child return. -/
theorem open_head_and_child_room (bits level : Nat) (profile : Profile)
    {row child : Nat}
    (rowInside : row < Forecast.scalar (Forecast.stageProfile profile))
    (childInside : child < Forecast.scalar (Forecast.stageProfile profile))
    (room : Room bits (Forecast.planProfile (level + 1) profile)) :
    Room bits
      ⟨SourceCurrentOpenRowReadResources.headGrowth (Forecast.scalar profile),
       SourceCurrentOpenRowReadResources.headGrowth (Forecast.scalar profile), profile.domains,
       SourceCurrentOpenRowReadResources.headGrowth (Forecast.scalar profile)⟩ ∧
    Room bits (Forecast.constructorProfile (Forecast.scalar profile) profile) ∧
    Room bits (Forecast.planProfile level (Forecast.scan (Forecast.planProfile level) child
      (Forecast.scan (Forecast.rowStep level (Forecast.scalar (Forecast.stageProfile profile))) row
        (Forecast.stageProfile profile)))) := by
  exact ⟨room.mono ((Forecast.stage_head_profile profile).trans (Forecast.plan_stage _ profile)),
    room.mono ((Forecast.stage_constructor_profile profile (Nat.le_refl _)).trans
      (Forecast.plan_stage _ profile)),
    room.mono (Forecast.plan_child_return level profile rowInside childInside)⟩

/-- A larger initial level and profile provide room for every smaller scheduled plan. -/
theorem larger_plan_reservation {bits firstLevel lastLevel : Nat} {first last : Profile}
    (levels : firstLevel ≤ lastLevel) (profiles : Le first last)
    (room : Room bits (Forecast.planProfile lastLevel last)) :
    Room bits first ∧ Room bits (Forecast.planProfile firstLevel first) := by
  have below := (Forecast.plan_mono firstLevel profiles).trans (Forecast.plan_level_mono levels last)
  have planned := room.mono below
  exact ⟨planned.mono (SourceCurrentConstrainedCapRequiredForecast.plan_ge _ _), planned⟩

end MicroCFTA.RequiredForecastIntegration
#print axioms MicroCFTA.RequiredForecastIntegration.open_head_and_child_room
#check @MicroCFTA.RequiredForecastIntegration.open_head_and_child_room
#print axioms MicroCFTA.RequiredForecastIntegration.larger_plan_reservation
#check @MicroCFTA.RequiredForecastIntegration.larger_plan_reservation
