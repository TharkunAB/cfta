import MicroCFTA.SourceCurrentConstrainedCapSharedMonotone
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.TargetMonotoneIntegration
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapSharedForecast (leafProfile leafFuel LeafReserved)
open SourceCurrentConstrainedCapSharedMonotone
open SourceCurrentConstrainedCapTargetForecast (targetProfile targetFuel TargetReserved)

private def paths : List (List Int) := [[1], [2], [0]]
private def stage (profile : Profile) (found : Bool) := leafProfile 3 paths found profile
private def schedule (profile : Profile) (first second third : Bool) := stage (stage (stage profile first) second) third
private def missOne (profile : Profile) := stage profile false
private def missTwo (profile : Profile) := stage (missOne profile) false
private def missThree (profile : Profile) := stage (missTwo profile) false

/-- Three arbitrary initial hit choices fit one all-miss schedule and its final room test. -/
theorem three_leaf_schedule (bits : Nat) (profile : Profile) (first second third : Bool) :
    Le (schedule profile first second third) (missThree profile) ∧
    leafFuel 3 paths first profile ≤ leafFuel 3 paths false profile ∧
    leafFuel 3 paths second (stage profile first) ≤ leafFuel 3 paths false (missOne profile) ∧
    leafFuel 3 paths third (stage (stage profile first) second) ≤ leafFuel 3 paths false (missTwo profile) ∧
    (Room bits (missThree profile) →
      LeafReserved bits 3 paths first profile ∧
      LeafReserved bits 3 paths second (stage profile first) ∧
      LeafReserved bits 3 paths third (stage (stage profile first) second)) := by
  have one := leafProfile_le_miss 3 paths first (Le.refl profile)
  have two := leafProfile_le_miss 3 paths second one
  have three := leafProfile_le_miss 3 paths third two
  refine ⟨three, leafFuel_le_miss 3 paths first (Le.refl profile),
    leafFuel_le_miss 3 paths second one, leafFuel_le_miss 3 paths third two, ?_⟩
  intro room
  have twoRoom := room.mono (SourceCurrentConstrainedCapSharedForecast.leafProfile_ge 3 paths false (missTwo profile))
  have oneRoom := twoRoom.mono (SourceCurrentConstrainedCapSharedForecast.leafProfile_ge 3 paths false (missOne profile))
  exact ⟨leafReserved_of_final_room bits 3 paths first profile oneRoom,
    leafReserved_of_miss bits 3 paths second one
      (leafReserved_of_final_room bits 3 paths false (missOne profile) twoRoom),
    leafReserved_of_miss bits 3 paths third two
      (leafReserved_of_final_room bits 3 paths false (missTwo profile) room)⟩

private def lower : Profile := ⟨2, 3, 1, 4⟩
private def upper : Profile := ⟨5, 8, 2, 9⟩
private theorem increased : Le lower upper := by
  unfold Le lower upper
  decide

/-- A literal rotated seed schedule preserves profile and fuel order and weakens reservations. -/
theorem rotated_target (bits : Nat) :
    Le (targetProfile 3 paths lower) (targetProfile 3 paths upper) ∧
    targetFuel 3 paths lower ≤ targetFuel 3 paths upper ∧
    (TargetReserved bits 3 paths upper → TargetReserved bits 3 paths lower) :=
  ⟨SourceCurrentConstrainedCapTargetMonotone.targetProfile_mono 3 paths increased,
    SourceCurrentConstrainedCapTargetMonotone.targetFuel_mono 3 paths increased,
    SourceCurrentConstrainedCapTargetMonotone.targetReserved_mono bits 3 paths increased⟩
end MicroCFTA.TargetMonotoneIntegration

#print axioms MicroCFTA.TargetMonotoneIntegration.three_leaf_schedule
#check @MicroCFTA.TargetMonotoneIntegration.three_leaf_schedule
#print axioms MicroCFTA.TargetMonotoneIntegration.rotated_target
#check @MicroCFTA.TargetMonotoneIntegration.rotated_target
