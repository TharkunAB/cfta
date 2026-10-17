import MicroCFTA.SourceCurrentConstrainedCapTargetForecast

/-!
# Initial forecasts for shared Force and Leaf calls

A present target slot keeps the initial profile. A missing slot uses the
Target forecast. Leaf then forecasts one native query at the Force return.
These schedules specify numeric bounds and entry reservations only.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSharedForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
local notation "Target" => SourceCurrentConstrainedCapTargetForecast
local notation "Forecast" => SourceCurrentAllocatedNativeResourceForecast.step

/-- A Force hit keeps its profile; a miss uses the selected Target schedule. -/
def forceProfile (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Profile :=
  if found then profile else Target.targetProfile count paths profile

/-- A Force miss reserves each query entry in its Target schedule. -/
def ForceReserved (bits count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Prop :=
  if found then True else Target.TargetReserved bits count paths profile

/-- A Force hit needs no Target fuel. -/
def forceFuel (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Nat :=
  if found then 0 else Target.targetFuel count paths profile

/-- A Leaf query starts at the profile returned by its Force schedule. -/
def leafProfile (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Profile :=
  Forecast (forceProfile count paths found profile)

/-- A Leaf reserves its Force schedule and the subsequent query entry. -/
def LeafReserved (bits count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Prop :=
  ForceReserved bits count paths found profile ∧ Room bits (forceProfile count paths found profile)

/-- One shared ceiling covers the Force and subsequent native query. -/
def leafFuel (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Nat :=
  max (forceFuel count paths found profile) (Target.queryFuel (forceProfile count paths found profile))

/-- A Force hit keeps the complete profile. -/
theorem forceProfile_hit (count : Nat) (paths : List (List Int)) (profile : Profile) :
    forceProfile count paths true profile = profile := rfl

/-- A Force miss uses the complete Target profile. -/
theorem forceProfile_miss (count : Nat) (paths : List (List Int)) (profile : Profile) :
    forceProfile count paths false profile = Target.targetProfile count paths profile := rfl

/-- A Force hit needs no reservation. -/
theorem forceReserved_hit (bits count : Nat) (paths : List (List Int)) (profile : Profile) :
    ForceReserved bits count paths true profile ↔ True := Iff.rfl

/-- A Force miss retains exactly the Target reservations. -/
theorem forceReserved_miss (bits count : Nat) (paths : List (List Int)) (profile : Profile) :
    ForceReserved bits count paths false profile ↔ Target.TargetReserved bits count paths profile := Iff.rfl

/-- A Force hit uses zero Target fuel. -/
theorem forceFuel_hit (count : Nat) (paths : List (List Int)) (profile : Profile) :
    forceFuel count paths true profile = 0 := rfl

/-- A Force miss uses exactly the Target fuel. -/
theorem forceFuel_miss (count : Nat) (paths : List (List Int)) (profile : Profile) :
    forceFuel count paths false profile = Target.targetFuel count paths profile := rfl

/-- A Leaf after a Force hit forecasts one query from the initial profile. -/
theorem leafProfile_hit (count : Nat) (paths : List (List Int)) (profile : Profile) :
    leafProfile count paths true profile = Forecast profile := rfl

/-- A Leaf after a Force miss forecasts one query from the Target return. -/
theorem leafProfile_miss (count : Nat) (paths : List (List Int)) (profile : Profile) :
    leafProfile count paths false profile = Forecast (Target.targetProfile count paths profile) := rfl

/-- A Leaf after a Force hit requires room only for its native query. -/
theorem leafReserved_hit (bits count : Nat) (paths : List (List Int)) (profile : Profile) :
    LeafReserved bits count paths true profile ↔ Room bits profile := by
  change (True ∧ Room bits profile) ↔ Room bits profile
  exact ⟨And.right, fun room => ⟨trivial, room⟩⟩

/-- A Leaf after a Force miss retains both reservation stages. -/
theorem leafReserved_miss (bits count : Nat) (paths : List (List Int)) (profile : Profile) :
    LeafReserved bits count paths false profile ↔
      Target.TargetReserved bits count paths profile ∧ Room bits (Target.targetProfile count paths profile) := Iff.rfl

/-- A Leaf after a Force hit uses exactly its native query fuel. -/
theorem leafFuel_hit (count : Nat) (paths : List (List Int)) (profile : Profile) :
    leafFuel count paths true profile = Target.queryFuel profile := Nat.zero_max _

/-- A Leaf after a Force miss covers the Target and its following query. -/
theorem leafFuel_miss (count : Nat) (paths : List (List Int)) (profile : Profile) :
    leafFuel count paths false profile =
      max (Target.targetFuel count paths profile) (Target.queryFuel (Target.targetProfile count paths profile)) := rfl

/-- A Force forecast retains each initial component bound. -/
theorem forceProfile_ge (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) :
    Le profile (forceProfile count paths found profile) := by
  cases found with
  | false => exact Target.targetProfile_ge count paths profile
  | true => exact Le.refl profile

/-- The Leaf forecast retains its Force return profile. -/
theorem forceProfile_le_leafProfile (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) :
    Le (forceProfile count paths found profile) (leafProfile count paths found profile) :=
  SourceCurrentAllocatedNativeResourceForecast.step_ge _

/-- A Leaf forecast retains each initial component bound. -/
theorem leafProfile_ge (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) :
    Le profile (leafProfile count paths found profile) :=
  (forceProfile_ge count paths found profile).trans (forceProfile_le_leafProfile count paths found profile)

/-- A Leaf reservation supplies the exact Force reservation. -/
theorem LeafReserved.force {bits count : Nat} {paths : List (List Int)} {found : Bool} {profile : Profile}
    (reserved : LeafReserved bits count paths found profile) : ForceReserved bits count paths found profile := reserved.1

/-- A Leaf reservation supplies room at the exact Force return profile. -/
theorem LeafReserved.query {bits count : Nat} {paths : List (List Int)} {found : Bool} {profile : Profile}
    (reserved : LeafReserved bits count paths found profile) : Room bits (forceProfile count paths found profile) := reserved.2

/-- The shared Leaf ceiling covers its Force fuel. -/
theorem leafFuel_force (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) :
    forceFuel count paths found profile ≤ leafFuel count paths found profile := Nat.le_max_left _ _

/-- The shared Leaf ceiling covers its query fuel at the Force return. -/
theorem leafFuel_query (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) :
    Target.queryFuel (forceProfile count paths found profile) ≤ leafFuel count paths found profile := Nat.le_max_right _ _

end MicroCFTA.SourceCurrentConstrainedCapSharedForecast
