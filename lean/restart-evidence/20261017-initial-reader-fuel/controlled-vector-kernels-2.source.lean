import MicroCFTA.HeightOrderControlled

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.ControlledVectorIntegration
open HeightOrderControlled

private def vector (low high index : Nat) : Nat :=
  if index = 0 then low else if index = 1 then high else 0

private theorem bounded (low high control : Nat) (lowFits : low ≤ control) (highFits : high ≤ control) :
    ∀ index, index < 2 → vector low high index ≤ control := by
  intro index inside
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa [vector] using lowFits
  · simpa [vector] using highFits

private theorem lower_step (low high : Nat) :
    HeightOrder.Below 2 (vector low high) (vector (low + 1) high) := by
  apply HeightOrder.below_of_decrease 2 _ _ 0 (by decide)
  · change low < low + 1
    omega
  · intro index above inside
    have same : index = 1 := by omega
    subst index
    exact Nat.le_refl _

private theorem countdown (control : Nat → Nat) (grows : ∀ value, value < control value)
    (count initial : Nat) (fits : count ≤ initial) :
    Path control 2 (vector count 0) initial (vector 0 0) (iterate control count initial) count := by
  induction count generalizing initial with
  | zero => exact .refl (bounded 0 0 initial (Nat.zero_le _) (Nat.zero_le _))
  | succ count ih =>
    have enough : count ≤ control initial := by have progress := grows initial; omega
    exact .step (bounded _ _ _ fits (Nat.zero_le _)) (lower_step count 0)
      (grows initial) (Nat.le_refl _) (ih _ enough)

private def doubling (value : Nat) : Nat := 2 * value + 1
private theorem doubling_mono {first last : Nat} (increase : first ≤ last) : doubling first ≤ doubling last := by
  unfold doubling
  omega
private theorem doubling_grows (value : Nat) : value < doubling value := by unfold doubling; omega

/-- An actual nine-step path exceeds the initial radix and raises a lower digit from zero to seven. -/
theorem reset_lower_digit :
    ∃ actual : Path doubling 2 (vector 1 1) 1 (vector 0 0) 1023 9,
      1 < 7 ∧ (1 + 1) ^ 2 < 9 ∧ 1023 ≤ majorant doubling 2 1 ∧ 9 ≤ majorant doubling 2 1 := by
  have tail := countdown doubling doubling_grows 7 7 (Nat.le_refl _)
  change Path doubling 2 (vector 7 0) 7 (vector 0 0) 1023 7 at tail
  have decrease : HeightOrder.Below 2 (vector 7 0) (vector 0 1) := by
    apply HeightOrder.below_of_decrease 2 _ _ 1 (by decide)
    · decide
    · intro index above inside
      omega
  have middle : Path doubling 2 (vector 0 1) 3 (vector 0 0) 1023 8 :=
    .step (bounded 0 1 3 (by decide) (by decide)) decrease (by decide) (by decide) tail
  have actual : Path doubling 2 (vector 1 1) 1 (vector 0 0) 1023 9 :=
    .step (bounded 1 1 1 (by decide) (by decide)) (lower_step 0 1) (by decide) (by decide) middle
  exact ⟨actual, by decide, by decide, actual.final_le doubling_mono doubling_grows,
    actual.length_le doubling_mono doubling_grows⟩

/-- An arbitrary growing monotone control permits a computed refill and its entire lower countdown. -/
theorem arbitrary_control_refill (control : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → control first ≤ control last)
    (grows : ∀ value, value < control value) (initial : Nat) (positive : 1 ≤ initial) :
    ∃ actual : Path control 2 (vector 0 1) initial (vector 0 0)
        (iterate control (control initial) (control initial)) (control initial + 1),
      initial < control initial ∧
      iterate control (control initial) (control initial) ≤ majorant control 2 initial ∧
      control initial + 1 ≤ majorant control 2 initial := by
  have tail := countdown control grows (control initial) (control initial) (Nat.le_refl _)
  have decrease : HeightOrder.Below 2 (vector (control initial) 0) (vector 0 1) := by
    apply HeightOrder.below_of_decrease 2 _ _ 1 (by decide)
    · decide
    · intro index above inside
      omega
  have actual : Path control 2 (vector 0 1) initial (vector 0 0)
      (iterate control (control initial) (control initial)) (control initial + 1) :=
    .step (bounded 0 1 initial (Nat.zero_le _) positive) decrease (grows initial) (Nat.le_refl _) tail
  exact ⟨actual, grows initial, actual.final_le mono grows, actual.length_le mono grows⟩

end MicroCFTA.ControlledVectorIntegration

#print axioms MicroCFTA.ControlledVectorIntegration.reset_lower_digit
#check @MicroCFTA.ControlledVectorIntegration.reset_lower_digit

#print axioms MicroCFTA.ControlledVectorIntegration.arbitrary_control_refill
#check @MicroCFTA.ControlledVectorIntegration.arbitrary_control_refill
