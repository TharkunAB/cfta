import MicroCFTA.SourceCurrentConstrainedCapTargetMonotone
import MicroCFTA.SourceCurrentConstrainedCapSharedForecast

/-!
# Shared forecasts bounded by the all-miss schedule

Larger initial profiles retain Force and Leaf bounds. The missing-slot
schedule bounds either initial slot branch. Its reservations therefore
supply both branches without a premise about any future stored target.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSharedMonotone
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapSharedForecast
namespace Target
export SourceCurrentConstrainedCapTargetMonotone
  (targetProfile_mono targetReserved_mono targetFuel_mono queryFuel_mono)
end Target

/-- Larger initial components retain the same Force branch profile. -/
theorem forceProfile_mono (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) :
    Le (forceProfile count paths found first) (forceProfile count paths found last) := by
  cases found with
  | false => exact Target.targetProfile_mono count paths increase
  | true => exact increase

/-- Larger initial components retain the Force return and subsequent query profile. -/
theorem leafProfile_mono (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) :
    Le (leafProfile count paths found first) (leafProfile count paths found last) :=
  SourceCurrentAllocatedNativeResourceForecast.step_mono (forceProfile_mono count paths found increase)

/-- Either Force branch fits the all-miss forecast of a larger initial profile. -/
theorem forceProfile_le_miss (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) :
    Le (forceProfile count paths found first) (forceProfile count paths false last) := by
  cases found with
  | false => exact Target.targetProfile_mono count paths increase
  | true => exact increase.trans (SourceCurrentConstrainedCapTargetForecast.targetProfile_ge count paths last)

/-- Either complete Leaf branch fits the all-miss forecast of a larger initial profile. -/
theorem leafProfile_le_miss (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) :
    Le (leafProfile count paths found first) (leafProfile count paths false last) :=
  SourceCurrentAllocatedNativeResourceForecast.step_mono (forceProfile_le_miss count paths found increase)

/-- A larger initial Force reservation supplies the same smaller branch. -/
theorem forceReserved_mono (bits count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) (reserved : ForceReserved bits count paths found last) :
    ForceReserved bits count paths found first := by
  cases found with
  | false => exact Target.targetReserved_mono bits count paths increase reserved
  | true => trivial

/-- A larger initial Leaf reservation supplies the same smaller branch and query. -/
theorem leafReserved_mono (bits count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) (reserved : LeafReserved bits count paths found last) :
    LeafReserved bits count paths found first :=
  ⟨forceReserved_mono bits count paths found increase reserved.1,
    reserved.2.mono (forceProfile_mono count paths found increase)⟩

/-- An all-miss Force reservation supplies either branch at a smaller initial profile. -/
theorem forceReserved_of_miss (bits count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) (reserved : ForceReserved bits count paths false last) :
    ForceReserved bits count paths found first := by
  cases found with
  | false => exact Target.targetReserved_mono bits count paths increase reserved
  | true => trivial

/-- An all-miss Leaf reservation supplies either branch at a smaller initial profile. -/
theorem leafReserved_of_miss (bits count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) (reserved : LeafReserved bits count paths false last) :
    LeafReserved bits count paths found first :=
  ⟨forceReserved_of_miss bits count paths found increase reserved.1,
    reserved.2.mono (forceProfile_le_miss count paths found increase)⟩

/-- Larger initial components retain the same Force branch fuel. -/
theorem forceFuel_mono (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) :
    forceFuel count paths found first ≤ forceFuel count paths found last := by
  cases found with
  | false => exact Target.targetFuel_mono count paths increase
  | true => exact Nat.le_refl _

/-- Larger initial components retain both stages of the same Leaf branch fuel. -/
theorem leafFuel_mono (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) : leafFuel count paths found first ≤ leafFuel count paths found last := by
  have force := forceFuel_mono count paths found increase
  have query := Target.queryFuel_mono (forceProfile_mono count paths found increase)
  unfold leafFuel
  omega

/-- The all-miss Force fuel covers either branch at a smaller initial profile. -/
theorem forceFuel_le_miss (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) : forceFuel count paths found first ≤ forceFuel count paths false last := by
  cases found with
  | false => exact Target.targetFuel_mono count paths increase
  | true => exact Nat.zero_le _

/-- The all-miss Leaf fuel covers either branch at a smaller initial profile. -/
theorem leafFuel_le_miss (count : Nat) (paths : List (List Int)) (found : Bool)
    {first last : Profile} (increase : Le first last) : leafFuel count paths found first ≤ leafFuel count paths false last := by
  have force := forceFuel_le_miss count paths found increase
  have query := Target.queryFuel_mono (forceProfile_le_miss count paths found increase)
  unfold leafFuel
  omega

/-- Room at the final all-miss Force profile supplies every earlier query reservation. -/
theorem forceReserved_of_final_room (bits count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile)
    (room : Room bits (forceProfile count paths false profile)) : ForceReserved bits count paths found profile := by
  have reserved : ForceReserved bits count paths false profile := by
    cases paths with
    | nil => trivial
    | cons seed paths =>
        exact SourceCurrentConstrainedCapTargetForecast.reserved_of_final_room bits count seed paths profile room
  exact forceReserved_of_miss bits count paths found (Le.refl profile) reserved

/-- One final all-miss Leaf room test supplies either Force branch and its following query. -/
theorem leafReserved_of_final_room (bits count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile)
    (room : Room bits (leafProfile count paths false profile)) : LeafReserved bits count paths found profile := by
  have earlier := room.mono (forceProfile_le_leafProfile count paths false profile)
  exact ⟨forceReserved_of_final_room bits count paths found profile earlier,
    earlier.mono (forceProfile_le_miss count paths found (Le.refl profile))⟩

end MicroCFTA.SourceCurrentConstrainedCapSharedMonotone
