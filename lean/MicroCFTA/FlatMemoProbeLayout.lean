import MicroCFTA.FlatMemoLayout
import MicroCFTA.FlatMemoProbe
import Init.Data.BitVec.Lemmas

/-!
# Source masked probe order

Power-of-two capacities make the source bit mask equal to modular wrapping.
The suffix-and-prefix traversal uses exactly those wrapped slot indices.
The raw hash function can choose any initial word; no hash quality is needed.
-/
namespace MicroCFTA.FlatMemoProbeLayout
open FlatMemoProbe

/-- Masking by one less than a power of two wraps an arbitrary hash or slot. -/
theorem mask_eq_mod (power value : Nat) :
    value &&& (2 ^ power - 1) = value % 2 ^ power :=
  Nat.and_two_pow_sub_one_eq_mod value power

/-- The source initial capacity is a power of two. -/
theorem initial_capacity : (1024 : Nat) = 2 ^ 10 := by decide

/-- Every permitted doubling retains a power-of-two capacity. -/
theorem doubled_capacity (power : Nat) : 2 * 2 ^ power = 2 ^ (power + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Word-level masking has the same natural slot index when the mask fits. -/
theorem word_mask (width power value : Nat) (fits : power ≤ width) :
    (BitVec.ofNat width value &&& BitVec.ofNat width (2 ^ power - 1)).toNat =
      value % 2 ^ power := by
  rw [← BitVec.ofNat_and, BitVec.toNat_ofNat, mask_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) fits))

/-- The mathematical source step increments the slot and applies the capacity mask. -/
def advance (power index : Nat) : Nat := (index + 1) &&& (2 ^ power - 1)

/-- Every source step stays within the allocated slot range. -/
theorem advance_bounded (power index : Nat) : advance power index < 2 ^ power := by
  rw [advance, mask_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Execute the source increment-and-mask operation a given number of times. -/
def steps (power start : Nat) : Nat → Nat
  | 0 => start
  | count + 1 => advance power (steps power start count)

/-- Repeated source steps visit the successive wrapped indices. -/
theorem iterate_advance (power start steps : Nat) :
    FlatMemoProbeLayout.steps power (start % 2 ^ power) steps = (start + steps) % 2 ^ power := by
  induction steps with
  | zero => simp [FlatMemoProbeLayout.steps]
  | succ steps ih =>
      rw [FlatMemoProbeLayout.steps, ih, advance, mask_eq_mod]
      rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Each element of the proof traversal is the matching wrapped source index. -/
theorem order_index (start : Fin capacity) (position : Nat) (valid : position < capacity) :
    ((order start)[position]'(by rw [order_length]; exact valid)).val =
      (start.val + position) % capacity := by
  unfold order
  by_cases suffix : position < capacity - start.val
  · rw [List.getElem_append_left (by simpa using suffix), List.getElem_drop]
    simp only [List.getElem_finRange]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [List.getElem_append_right (by simp; omega), List.getElem_take]
    simp only [List.getElem_finRange, List.length_drop, List.length_finRange, Fin.val_cast]
    have small : start.val + position - capacity < capacity := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt small]
    omega

/-- The bounded proof traversal is the exact source sequence from any masked hash word. -/
theorem order_source (power hash position : Nat) (valid : position < 2 ^ power) :
    let start : Fin (2 ^ power) := ⟨hash &&& (2 ^ power - 1), by
      rw [mask_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    ((order start)[position]'(by rw [order_length]; exact valid)).val =
      steps power (hash % 2 ^ power) position := by
  dsimp only
  rw [order_index _ position valid, iterate_advance]
  simp only [mask_eq_mod, Nat.add_mod, Nat.mod_mod]

end MicroCFTA.FlatMemoProbeLayout
