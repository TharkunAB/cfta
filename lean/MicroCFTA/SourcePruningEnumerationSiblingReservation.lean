import MicroCFTA.SourcePruningEnumerationRecursiveReservation

/-!
# Original reservations for ordered sibling callbacks

Each stage pays one edge and its depth-one callback. The next stage uses
the preceding forecast. Captured mass and inherited bucket bounds stay
fixed across siblings. This schedule does not assert execution success.
-/
namespace MicroCFTA.SourcePruningEnumerationSiblingReservation
open SourceCurrentAllocatedNativeResourceForecast (Le Room)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationRecursiveReservation (afterHook)
attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHook

/-- Iterate the paired edge and callback forecast in sibling order. -/
noncomputable def stage (seed : Seed) (capturedMass inherited : Nat) : Nat → Seed
  | 0 => seed
  | count + 1 => stage (afterHook seed capturedMass inherited) capturedMass inherited count

/-- An empty sibling schedule retains its original seed. -/
theorem stage_zero (seed : Seed) (capturedMass inherited : Nat) :
    stage seed capturedMass inherited 0 = seed := rfl

/-- The first paired forecast precedes the remaining sibling stages. -/
theorem stage_succ (seed : Seed) (capturedMass inherited count : Nat) :
    stage seed capturedMass inherited (count + 1) =
      stage (afterHook seed capturedMass inherited) capturedMass inherited count := rfl

/-- Consecutive parts compose at the exact scheduled intermediate seed. -/
theorem stage_add (seed : Seed) (capturedMass inherited first last : Nat) :
    stage seed capturedMass inherited (first + last) =
      stage (stage seed capturedMass inherited first) capturedMass inherited last := by
  induction first generalizing seed with
  | zero => simp only [Nat.zero_add, stage]
  | succ first ih => simpa only [Nat.succ_add, stage] using ih (afterHook seed capturedMass inherited)

/-- One final paired forecast follows the preceding stages. -/
theorem stage_succ_right (seed : Seed) (capturedMass inherited count : Nat) :
    stage seed capturedMass inherited (count + 1) =
      afterHook (stage seed capturedMass inherited count) capturedMass inherited :=
  stage_add seed capturedMass inherited count 1

/-- Every stage retains the original numeric profile and guard alphabet. -/
theorem stage_ge (seed : Seed) (capturedMass inherited count : Nat) :
    Le seed.2 (stage seed capturedMass inherited count).2 ∧
      seed.1 ⊆ (stage seed capturedMass inherited count).1 := by
  induction count generalizing seed with
  | zero => exact ⟨Le.refl _, fun _ member => member⟩
  | succ count ih =>
      have first := SourcePruningEnumerationRecursiveReservation.afterHook_ge seed capturedMass inherited
      have later := ih (afterHook seed capturedMass inherited)
      exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩

/-- A later stage of this same schedule retains every earlier numeric and guard bound. -/
theorem count_mono (seed : Seed) (capturedMass inherited : Nat) {first last : Nat}
    (counts : first ≤ last) :
    Le (stage seed capturedMass inherited first).2 (stage seed capturedMass inherited last).2 ∧
      (stage seed capturedMass inherited first).1 ⊆ (stage seed capturedMass inherited last).1 := by
  obtain ⟨extra, same⟩ := Nat.exists_eq_add_of_le counts
  rw [same, stage_add]
  exact stage_ge (stage seed capturedMass inherited first) capturedMass inherited extra

/-- Reserve both phases at every original sibling entry. -/
def Reserved (bits : Nat) (seed : Seed) (capturedMass inherited count : Nat) : Prop :=
  ∀ index, index < count →
    SourcePruningEnumerationRecursiveReservation.Reserved bits
      (stage seed capturedMass inherited index) capturedMass inherited

/-- An empty sibling list needs no phase reservation. -/
theorem reserved_zero (bits : Nat) (seed : Seed) (capturedMass inherited : Nat) :
    Reserved bits seed capturedMass inherited 0 := by
  intro index less
  omega

/-- The first paired reservation and remaining sibling reservations describe a nonempty schedule. -/
theorem reserved_succ_iff (bits : Nat) (seed : Seed) (capturedMass inherited count : Nat) :
    Reserved bits seed capturedMass inherited (count + 1) ↔
      SourcePruningEnumerationRecursiveReservation.Reserved bits seed capturedMass inherited ∧
        Reserved bits (afterHook seed capturedMass inherited) capturedMass inherited count := by
  constructor
  · intro reservation
    exact ⟨reservation 0 (by omega), fun index less => reservation (index + 1) (by omega)⟩
  · rintro ⟨first, rest⟩ index less
    cases index with
    | zero => exact first
    | succ index => exact rest index (by omega)

/-- A nonempty sibling reservation supplies both phases of its first sibling. -/
theorem Reserved.head {bits capturedMass inherited count : Nat} {seed : Seed}
    (reservation : Reserved bits seed capturedMass inherited (count + 1)) :
    SourcePruningEnumerationRecursiveReservation.Reserved bits seed capturedMass inherited :=
  ((reserved_succ_iff bits seed capturedMass inherited count).mp reservation).1

/-- The remaining siblings use the seed after the first complete paired forecast. -/
theorem Reserved.tail {bits capturedMass inherited count : Nat} {seed : Seed}
    (reservation : Reserved bits seed capturedMass inherited (count + 1)) :
    Reserved bits (afterHook seed capturedMass inherited) capturedMass inherited count :=
  ((reserved_succ_iff bits seed capturedMass inherited count).mp reservation).2

/-- A longer reservation covers every shorter initial part of the same schedule. -/
theorem Reserved.prefix {bits capturedMass inherited first last : Nat} {seed : Seed}
    (reservation : Reserved bits seed capturedMass inherited last) (counts : first ≤ last) :
    Reserved bits seed capturedMass inherited first :=
  fun index less => reservation index (Nat.lt_of_lt_of_le less counts)

/-- A consumed schedule prefix retains the original reservation for its remaining siblings. -/
theorem Reserved.after_prefix {bits capturedMass inherited consumed remaining : Nat} {seed : Seed}
    (reservation : Reserved bits seed capturedMass inherited (consumed + remaining)) :
    Reserved bits (stage seed capturedMass inherited consumed) capturedMass inherited remaining := by
  intro index less
  have current := reservation (consumed + index) (by omega)
  simpa only [stage_add] using current

/-- Room at the final original forecast supplies every paired sibling reservation. -/
theorem reserved_of_final_room (bits : Nat) (seed : Seed) (capturedMass inherited count : Nat)
    (room : Room bits (stage seed capturedMass inherited count).2) :
    Reserved bits seed capturedMass inherited count := by
  intro index less
  have current : Room bits (stage seed capturedMass inherited (index + 1)).2 :=
    room.mono (count_mono seed capturedMass inherited (by omega : index + 1 ≤ count)).1
  rw [stage_succ_right] at current
  exact SourcePruningEnumerationRecursiveReservation.reserved_of_final_room bits
    (stage seed capturedMass inherited index) capturedMass inherited current

/-- The original finite schedule computes a mathematical width for all sibling phases. -/
theorem reserved_computed (seed : Seed) (capturedMass inherited count : Nat) :
    Reserved (SourceCurrentParentInitialRoom.roomBits (stage seed capturedMass inherited count).2)
      seed capturedMass inherited count :=
  reserved_of_final_room _ seed capturedMass inherited count (SourceCurrentParentInitialRoom.room_computed _)

end MicroCFTA.SourcePruningEnumerationSiblingReservation
