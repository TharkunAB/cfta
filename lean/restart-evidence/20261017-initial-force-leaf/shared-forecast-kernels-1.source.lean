import MicroCFTA.SourceCurrentConstrainedCapSharedForecast

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option linter.all true

namespace MicroCFTA.SharedForecastKernels
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapSharedForecast
open SourceCurrentConstrainedCapTargetForecast (operand queryFuel)

/-- A present slot removes all Target work but retains the Leaf query. -/
theorem present_slot (bits count : Nat) (paths : List (List Int)) (profile : Profile)
    (room : Room bits profile) :
    forceProfile count paths true profile = profile ∧
      forceFuel count paths true profile = 0 ∧
      LeafReserved bits count paths true profile ∧
      leafFuel count paths true profile = queryFuel profile ∧
      Le profile (leafProfile count paths true profile) :=
  ⟨rfl, rfl, ⟨trivial, room⟩, leafFuel_hit count paths profile,
    leafProfile_ge count paths true profile⟩

/-- An empty missing Target keeps its input and reserves only the following query. -/
theorem empty_missing_target (bits count : Nat) (profile : Profile) (room : Room bits profile) :
    forceProfile count [] false profile = profile ∧
      forceFuel count [] false profile = 0 ∧
      LeafReserved bits count [] false profile ∧
      leafFuel count [] false profile = queryFuel profile :=
  ⟨rfl, rfl, ⟨trivial, room⟩, Nat.zero_max _⟩

/-- A singleton miss followed by a hit forecasts two distinct query entries. -/
theorem singleton_miss_then_hit (bits count : Nat) (seed : List Int) (profile : Profile)
    (room : Room bits (SourceCurrentAllocatedNativeResourceForecast.step
      (SourceCurrentAllocatedNativeResourceForecast.step (operand seed count profile)))) :
    let first := leafProfile count [seed] false profile
    LeafReserved bits count [seed] false profile ∧
      LeafReserved bits count [seed] true first ∧
      leafProfile count [seed] true first = SourceCurrentAllocatedNativeResourceForecast.step
        (SourceCurrentAllocatedNativeResourceForecast.step (operand seed count profile)) ∧
      Le profile (leafProfile count [seed] true first) := by
  dsimp only
  have firstRoom : Room bits (leafProfile count [seed] false profile) :=
    room.mono (forceProfile_le_leafProfile count [seed] true _)
  have targetRoom : Room bits (forceProfile count [seed] false profile) :=
    firstRoom.mono (forceProfile_le_leafProfile count [seed] false profile)
  exact ⟨⟨trivial, targetRoom⟩, ⟨trivial, firstRoom⟩, rfl,
    (leafProfile_ge count [seed] false profile).trans (leafProfile_ge count [seed] true _)⟩

end MicroCFTA.SharedForecastKernels

#print axioms MicroCFTA.SharedForecastKernels.present_slot
#check @MicroCFTA.SharedForecastKernels.present_slot
#print axioms MicroCFTA.SharedForecastKernels.empty_missing_target
#check @MicroCFTA.SharedForecastKernels.empty_missing_target
#print axioms MicroCFTA.SharedForecastKernels.singleton_miss_then_hit
#check @MicroCFTA.SharedForecastKernels.singleton_miss_then_hit
