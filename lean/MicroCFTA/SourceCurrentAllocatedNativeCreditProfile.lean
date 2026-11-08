import MicroCFTA.SourceCurrentAllocatedNativeResourceForecast

/-!
# Native query entry credit and final counter capacity

Entry reserves one query's initial instruction bound. Capacity checks only
the counters of a final forecast. A final profile that bounds one complete
step supplies Entry at that step's source. Admits retains the earlier Room
certificate as an alternative. The numeric forecast is unchanged.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCreditProfile
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room step)
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound

/-- One native query has room for its initial instruction credit. -/
def Entry (bits : Nat) (profile : Profile) : Prop :=
  profile.nodes < 2 ^ bits ∧ profile.edges ≤ 2 ^ (bits + 2) ∧
    profile.domains + instructionBound profile.nodes profile.edges profile.mass < 2 ^ (bits + 1)

/-- A final forecast keeps its three counters within the modeled widths. -/
def Capacity (bits : Nat) (profile : Profile) : Prop :=
  profile.nodes < 2 ^ bits ∧ profile.edges ≤ 2 ^ (bits + 2) ∧ profile.domains < 2 ^ (bits + 1)

/-- Either proved entry certificate admits the same actual native query. -/
def Admits (bits : Nat) (profile : Profile) : Prop := Room bits profile ∨ Entry bits profile

/-- A smaller entry profile needs no more instruction credit. -/
theorem Entry.mono {bits : Nat} {first last : Profile} (room : Entry bits last) (below : Le first last) :
    Entry bits first := by
  have instructions := SourceCurrentAllocatedNativeComputedBudget.instructionBound_mono
    below.1 below.2.1 below.2.2.2
  exact ⟨Nat.lt_of_le_of_lt below.1 room.1, Nat.le_trans below.2.1 room.2.1,
    Nat.lt_of_le_of_lt (Nat.add_le_add below.2.2.1 instructions) room.2.2⟩

/-- A smaller final profile retains all three counter bounds. -/
theorem Capacity.mono {bits : Nat} {first last : Profile} (room : Capacity bits last) (below : Le first last) :
    Capacity bits first :=
  ⟨Nat.lt_of_le_of_lt below.1 room.1, Nat.le_trans below.2.1 room.2.1,
    Nat.lt_of_le_of_lt below.2.2.1 room.2.2⟩

/-- The earlier Room certificate also bounds its three counters. -/
theorem capacity_of_room {bits : Nat} {profile : Profile} (room : Room bits profile) : Capacity bits profile :=
  ⟨room.1, room.2.1, Nat.lt_of_le_of_lt (Nat.le_add_right _ _) room.2.2⟩

/-- A completed forecast step supplies its own entry credit from final counter capacity. -/
theorem entry_of_step_capacity {bits : Nat} {first last : Profile}
    (below : Le (step first) last) (room : Capacity bits last) : Entry bits first := by
  have initial := (SourceCurrentAllocatedNativeResourceForecast.step_ge first).trans below
  exact ⟨Nat.lt_of_le_of_lt initial.1 room.1, Nat.le_trans initial.2.1 room.2.1,
    Nat.lt_of_le_of_lt below.2.2.1 room.2.2⟩

/-- Both admission alternatives retain smaller actual entry profiles. -/
theorem Admits.mono {bits : Nat} {first last : Profile} (room : Admits bits last) (below : Le first last) :
    Admits bits first := by
  rcases room with old | credit
  · exact Or.inl (old.mono below)
  · exact Or.inr (credit.mono below)

end MicroCFTA.SourceCurrentAllocatedNativeCreditProfile
