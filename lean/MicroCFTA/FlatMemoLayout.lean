import MicroCFTA.DecoderMachineBounds

/-!
# Native layout bounds for the flat memo table

On the validated 64-bit host, each slot has three eight-byte key words.
The source allocates 24 bytes per slot. These arithmetic results require
the byte allocation to fit a nonnegative signed machine word. They do not
prove that the runtime allocation succeeds or that atomic access is ordered.
-/
namespace MicroCFTA.FlatMemoLayout
open DecoderMachineBounds

/-- Every source key offset selects one of the three allocated words of a valid slot. -/
theorem key_offset (capacity slot field : Nat) (valid : slot < capacity) (component : field < 3) :
    3 * slot + field < 3 * capacity ∧ 8 * (3 * slot + field) + 7 < 24 * capacity := by omega

/-- A fitting byte allocation makes every native index and byte offset fit too. -/
theorem index_fits (bits capacity slot field : Nat) (allocation : 24 * capacity ≤ maximum bits)
    (valid : slot < capacity) (component : field < 3) :
    slot ≤ maximum bits ∧ 3 * slot + field ≤ maximum bits ∧
      8 * (3 * slot + field) + 7 ≤ maximum bits := by
  have bounds := key_offset capacity slot field valid component
  omega

/-- The source byte allocation multiplication is exact under its explicit size bound. -/
theorem allocation_word (bits capacity : Nat) (allocation : 24 * capacity ≤ maximum bits) :
    signed bits (multiply bits (cast bits 24) (cast bits capacity)) = ((24 * capacity : Nat) : Int) :=
  multiply_exact bits 24 capacity allocation

/-- Source slot indexing uses exact signed multiplication and addition inside the allocated range. -/
theorem offset_word (bits capacity slot field : Nat) (allocation : 24 * capacity ≤ maximum bits)
    (valid : slot < capacity) (component : field < 3) :
    signed bits (add bits (multiply bits (cast bits 3) (cast bits slot)) (cast bits field)) =
      ((3 * slot + field : Nat) : Int) := by
  rw [multiply_cast, add_cast]
  exact narrow_exact bits _ (index_fits bits capacity slot field allocation valid component).2.1

/-- The negative missing-slot encoding and its source decoding are exact integer inverses. -/
theorem missing_slot (slot : Nat) : (-1 : Int) - (-1 - (slot : Int)) = (slot : Int) := by omega

/-- A valid missing-slot code stays within the signed range and cannot be a found index. -/
theorem missing_slot_range (bits capacity slot : Nat) (allocation : 24 * capacity ≤ maximum bits)
    (valid : slot < capacity) :
    -(half bits : Int) ≤ (-1 : Int) - (slot : Int) ∧ (-1 : Int) - (slot : Int) < 0 := by
  have fits := (index_fits bits capacity slot 0 allocation valid (by omega)).1
  have relation := maximum_succ bits
  omega

/-- Reserving the doubled arrays also bounds all old capacity and load-factor arithmetic. -/
theorem growth_fits (bits capacity count : Nat) (positive : 0 < capacity)
    (allocation : 48 * capacity ≤ maximum bits) (halfFull : 2 * count ≤ capacity) :
    24 * (2 * capacity) ≤ maximum bits ∧
      2 * capacity ≤ maximum bits ∧
      2 * (count + 1) ≤ maximum bits ∧ capacity - 1 ≤ maximum bits := by omega

/-- The source capacity doubling retains its exact signed value before a permitted growth. -/
theorem growth_word (bits capacity : Nat) (allocation : 48 * capacity ≤ maximum bits) :
    signed bits (multiply bits (cast bits 2) (cast bits capacity)) = ((2 * capacity : Nat) : Int) :=
  multiply_exact bits 2 capacity (by omega)

/-- A non-growing insertion preserves half occupancy; a growth provides room for that insertion. -/
theorem occupancy_after_insert (capacity count : Nat) (positive : 0 < capacity)
    (halfFull : 2 * count ≤ capacity) :
    (¬2 * (count + 1) > capacity → 2 * (count + 1) ≤ capacity) ∧
      (2 * (count + 1) > capacity → 2 * (count + 1) ≤ 2 * capacity) := by omega

end MicroCFTA.FlatMemoLayout
