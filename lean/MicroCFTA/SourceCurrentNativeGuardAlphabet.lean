import MicroCFTA.SourceEqualityPCSNativeEdge

/-!
# Finite source guard alphabets across finite schedules

One step retains the entry alphabet, Top, and each ordered conjunction of
two entry guards. Iteration uses an abstract extension count. These pure list
laws do not assert a physical query result or guard preservation.
-/
namespace MicroCFTA.SourceCurrentNativeGuardAlphabet
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- One alphabet extension retains all entry guards and each possible primitive guard. -/
noncomputable def step (alphabet : List Guard) : List Guard :=
  alphabet ++ [top] ++ alphabet.flatMap (fun first => alphabet.map (conjoin first))

/-- Every entry guard remains in the next alphabet. -/
theorem mem_step_of_mem {alphabet : List Guard} {guard : Guard} (member : guard ∈ alphabet) :
    guard ∈ step alphabet := by
  exact List.mem_append_left _ (List.mem_append_left _ member)

/-- Top is in every next alphabet, including an empty entry alphabet. -/
theorem top_mem_step (alphabet : List Guard) : top ∈ step alphabet := by
  exact List.mem_append_left _ (List.mem_append_right _ (by simp))

/-- Each literal ordered pair of entry guards contributes its actual source conjunction. -/
theorem conjoin_mem_step {alphabet : List Guard} {first second : Guard}
    (left : first ∈ alphabet) (right : second ∈ alphabet) : conjoin first second ∈ step alphabet := by
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨first, left, List.mem_map.mpr ⟨second, right, rfl⟩⟩)

/-- Alphabet inclusion is sufficient for inclusion of the next alphabet. -/
theorem step_mono {first last : List Guard} (increase : first ⊆ last) : step first ⊆ step last := by
  intro guard member
  rcases List.mem_append.mp member with earlier | pair
  · rcases List.mem_append.mp earlier with original | unit
    · exact mem_step_of_mem (increase original)
    · have same : guard = top := by simpa only [List.mem_singleton] using unit
      exact same ▸ top_mem_step last
  · obtain ⟨left, leftIn, rightIn⟩ := List.mem_flatMap.mp pair
    obtain ⟨right, memberRight, same⟩ := List.mem_map.mp rightIn
    rw [← same]
    exact conjoin_mem_step (increase leftIn) (increase memberRight)

/-- The literal list retains duplicates and has one entry for each ordered pair. -/
theorem step_length (alphabet : List Guard) :
    (step alphabet).length = alphabet.length + 1 + alphabet.length * alphabet.length := by
  simp [step, List.length_flatMap, List.map_const', List.sum_replicate_nat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The next alphabet retains the length of the entry list. -/
theorem step_length_ge (alphabet : List Guard) : alphabet.length ≤ (step alphabet).length := by
  rw [step_length]
  omega

/-- A fixed extension count determines a finite alphabet before execution. -/
noncomputable def advance (alphabet : List Guard) : Nat → List Guard
  | 0 => alphabet
  | count + 1 => advance (step alphabet) count

/-- A zero count retains the exact entry list. -/
theorem advance_zero (alphabet : List Guard) : advance alphabet 0 = alphabet := rfl

/-- Each successor advances the entry alphabet once before the remaining schedule. -/
theorem advance_succ (alphabet : List Guard) (count : Nat) :
    advance alphabet (count + 1) = advance (step alphabet) count := rfl

/-- Finite schedules compose in the same extension order. -/
theorem advance_add (alphabet : List Guard) (first last : Nat) :
    advance alphabet (first + last) = advance (advance alphabet first) last := by
  induction first generalizing alphabet with
  | zero => simp only [Nat.zero_add, advance_zero]
  | succ first ih =>
      simpa only [Nat.succ_add, advance_succ] using ih (step alphabet)

/-- The final extension can also advance the already computed prefix alphabet. -/
theorem advance_step (alphabet : List Guard) (count : Nat) :
    advance alphabet (count + 1) = step (advance alphabet count) := by
  simpa only [advance_succ, advance_zero] using advance_add alphabet count 1

/-- Every original guard remains in each finite extension schedule. -/
theorem mem_advance_of_mem {alphabet : List Guard} {guard : Guard} (member : guard ∈ alphabet)
    (count : Nat) : guard ∈ advance alphabet count := by
  induction count generalizing alphabet with
  | zero => exact member
  | succ count ih => exact ih (mem_step_of_mem member)

/-- Inclusion of initial alphabets gives inclusion at the same extension count. -/
theorem advance_mono {first last : List Guard} (increase : first ⊆ last) (count : Nat) :
    advance first count ⊆ advance last count := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih (step_mono increase)

/-- More extensions retain every guard from a shorter schedule. -/
theorem advance_count_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) :
    advance alphabet first ⊆ advance alphabet last := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increase
  rw [advance_add]
  exact fun _ member => mem_advance_of_mem member extra

/-- Ordered pairs in the prefix alphabet belong to the next scheduled alphabet. -/
theorem conjoin_mem_advance {alphabet : List Guard} {first second : Guard} (count : Nat)
    (left : first ∈ advance alphabet count) (right : second ∈ advance alphabet count) :
    conjoin first second ∈ advance alphabet (count + 1) := by
  rw [advance_step]
  exact conjoin_mem_step left right

/-- Every nonempty extension schedule contains Top. -/
theorem top_mem_advance (alphabet : List Guard) {count : Nat} (positive : 0 < count) :
    top ∈ advance alphabet count := by
  cases count with
  | zero => omega
  | succ count => exact mem_advance_of_mem (top_mem_step alphabet) count

/-- Every finite schedule retains the original list length. -/
theorem advance_length_ge (alphabet : List Guard) (count : Nat) :
    alphabet.length ≤ (advance alphabet count).length := by
  induction count generalizing alphabet with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (step_length_ge alphabet) (ih (step alphabet))

/-- The literal alphabet length increases with the scheduled extension count. -/
theorem advance_length_count_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) :
    (advance alphabet first).length ≤ (advance alphabet last).length := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increase
  rw [advance_add]
  exact advance_length_ge _ extra

end MicroCFTA.SourceCurrentNativeGuardAlphabet
