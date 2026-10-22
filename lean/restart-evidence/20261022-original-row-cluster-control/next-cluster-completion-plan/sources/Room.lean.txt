import MicroCFTA.SourceCurrentAllocatedNativeComputedBudget
import MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone

/-!
# Initial resource forecasts for finite native query sequences

The profile records numeric upper bounds. One step uses the computed native
instruction bound and the causal mass schedule. A reservation checks only
query entry states. It does not assert a physical execution or a source law.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeResourceForecast

local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter

/-- Numeric upper bounds for one query entry. -/
structure Profile where
  /-- Upper bound on the issued node counter. -/
  nodes : Nat
  /-- Upper bound on the issued edge counter. -/
  edges : Nat
  /-- Upper bound on the domain counter. -/
  domains : Nat
  /-- Upper bound on every stored payload mass. -/
  mass : Nat

/-- Each component of the first profile is at most the second component. -/
def Le (first last : Profile) : Prop :=
  first.nodes ≤ last.nodes ∧ first.edges ≤ last.edges ∧
    first.domains ≤ last.domains ∧ first.mass ≤ last.mass

/-- A profile bounds itself. -/
theorem Le.refl (profile : Profile) : Le profile profile :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Component bounds compose. -/
theorem Le.trans {first middle last : Profile} (one : Le first middle) (two : Le middle last) :
    Le first last :=
  ⟨Nat.le_trans one.1 two.1, Nat.le_trans one.2.1 two.2.1,
    Nat.le_trans one.2.2.1 two.2.2.1, Nat.le_trans one.2.2.2 two.2.2.2⟩

/-- Forecast one query with the complete initial instruction and mass bounds. -/
def step (profile : Profile) : Profile :=
  let instructions := instructionBound profile.nodes profile.edges profile.mass
  let constructors := credit instructions profile.mass
  ⟨profile.nodes + constructors, profile.edges + constructors,
    profile.domains + instructions, massAfter instructions profile.mass⟩

/-- One forecast retains each initial component bound. -/
theorem step_ge (profile : Profile) : Le profile (step profile) :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
    SourceCurrentAllocatedRecursiveMassTrace.massAfter_ge _ _⟩

/-- A larger initial profile retains the one-query forecast. -/
theorem step_mono {first last : Profile} (increase : Le first last) : Le (step first) (step last) := by
  have instructions := SourceCurrentAllocatedNativeComputedBudget.instructionBound_mono
    increase.1 increase.2.1 increase.2.2.2
  have constructors := SourceCurrentAllocatedRecursiveMassMonotone.credit_mono
    instructions increase.2.2.2
  exact ⟨Nat.add_le_add increase.1 constructors, Nat.add_le_add increase.2.1 constructors,
    Nat.add_le_add increase.2.2.1 instructions,
    SourceCurrentAllocatedRecursiveMassMonotone.massAfter_mono instructions increase.2.2.2⟩

/-- Forecast a fixed number of queries from the original profile. -/
def advance (profile : Profile) : Nat → Profile
  | 0 => profile
  | count + 1 => advance (step profile) count

/-- An empty query sequence retains the original profile. -/
theorem advance_zero (profile : Profile) : advance profile 0 = profile := rfl

/-- A nonempty query sequence starts with one forecast step. -/
theorem advance_succ (profile : Profile) (count : Nat) :
    advance profile (count + 1) = advance (step profile) count := rfl

/-- Two consecutive query forecasts compose in source order. -/
theorem advance_add (profile : Profile) (first last : Nat) :
    advance profile (first + last) = advance (advance profile first) last := by
  induction first generalizing profile with
  | zero => simp only [Nat.zero_add, advance]
  | succ first ih => simpa only [Nat.succ_add, advance] using ih (step profile)

/-- A finite query forecast retains every original component bound. -/
theorem advance_ge (profile : Profile) (count : Nat) : Le profile (advance profile count) := by
  induction count generalizing profile with
  | zero => exact Le.refl _
  | succ count ih => exact (step_ge profile).trans (ih (step profile))

/-- A larger original profile retains every fixed query forecast. -/
theorem advance_mono {first last : Profile} (increase : Le first last) (count : Nat) :
    Le (advance first count) (advance last count) := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih (step_mono increase)

/-- Additional forecast queries retain all earlier component bounds. -/
theorem advance_count_mono (profile : Profile) {first last : Nat} (counts : first ≤ last) :
    Le (advance profile first) (advance profile last) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
  rw [advance_add]
  exact advance_ge _ extra

/-- Numeric entry conditions for the checked native query at this width. -/
def Room (bits : Nat) (profile : Profile) : Prop :=
  profile.nodes < 2 ^ bits ∧ profile.edges ≤ 2 ^ (bits + 2) ∧
    profile.domains + 2 ^ (profile.nodes + profile.nodes * profile.nodes) < 2 ^ (bits + 1)

/-- Entry room for a larger profile gives entry room for a smaller profile. -/
theorem Room.mono {bits : Nat} {first last : Profile} (room : Room bits last)
    (below : Le first last) : Room bits first := by
  have exponent := Nat.add_le_add below.1 (Nat.mul_le_mul below.1 below.1)
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2) exponent
  exact ⟨Nat.lt_of_le_of_lt below.1 room.1, Nat.le_trans below.2.1 room.2.1,
    Nat.lt_of_le_of_lt (Nat.add_le_add below.2.2.1 power) room.2.2⟩

/-- The original forecast has entry room for each query in a finite sequence. -/
def Reserved (bits : Nat) (profile : Profile) (count : Nat) : Prop :=
  ∀ index, index < count → Room bits (advance profile index)

/-- An empty query sequence requires no entry room. -/
theorem reserved_zero (bits : Nat) (profile : Profile) : Reserved bits profile 0 := by
  intro index less
  omega

/-- A nonempty reservation gives initial entry room and a reservation after one forecast. -/
theorem reserved_succ_iff (bits : Nat) (profile : Profile) (count : Nat) :
    Reserved bits profile (count + 1) ↔ Room bits profile ∧ Reserved bits (step profile) count := by
  constructor
  · intro reservation
    exact ⟨reservation 0 (by omega), fun index less => reservation (index + 1) (by omega)⟩
  · rintro ⟨room, reservation⟩ index less
    cases index with
    | zero => exact room
    | succ index => exact reservation index (by omega)

/-- A nonempty reservation supplies room for its first query. -/
theorem Reserved.head {bits count : Nat} {profile : Profile}
    (reservation : Reserved bits profile (count + 1)) : Room bits profile :=
  ((reserved_succ_iff bits profile count).mp reservation).1

/-- A nonempty reservation retains the remaining queries after one forecast. -/
theorem Reserved.tail {bits count : Nat} {profile : Profile}
    (reservation : Reserved bits profile (count + 1)) : Reserved bits (step profile) count :=
  ((reserved_succ_iff bits profile count).mp reservation).2

/-- A reservation for a larger profile applies to a smaller profile. -/
theorem Reserved.mono {bits count : Nat} {first last : Profile}
    (reservation : Reserved bits last count) (below : Le first last) : Reserved bits first count :=
  fun index less => (reservation index less).mono (advance_mono below index)

/-- A finite reservation applies to every shorter initial query sequence. -/
theorem Reserved.prefix {bits first last : Nat} {profile : Profile}
    (reservation : Reserved bits profile last) (counts : first ≤ last) : Reserved bits profile first :=
  fun index less => reservation index (Nat.lt_of_lt_of_le less counts)

/-- One numeric test at the last query entry supplies the full finite reservation. -/
theorem reserved_iff_last (bits : Nat) (profile : Profile) (count : Nat) :
    Reserved bits profile (count + 1) ↔ Room bits (advance profile count) := by
  constructor
  · intro reservation
    exact reservation count (by omega)
  · intro room index less
    exact room.mono (advance_count_mono profile (by omega))

end MicroCFTA.SourceCurrentAllocatedNativeResourceForecast
