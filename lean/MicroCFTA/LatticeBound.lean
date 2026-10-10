import MicroCFTA.LatticeLinear
import MicroCFTA.PolynomialSupport

/-!
# Unit-coefficient bound extraction

The source removes the selected variable from a linear inequality. Coefficient
one gives a lower bound. Coefficient minus one gives an upper bound. Every
other coefficient reports the source's unsupported-bound error.
-/

namespace MicroCFTA.LatticeBound

open LatticeLinear

/-- Replace the selected integer variable and keep all other variable values. -/
def update (assignment : Nat → Int) (index : Nat) (value : Int) : Nat → Int :=
  fun other => if other = index then value else assignment other

/-- Read a coefficient from the ordered sparse map, using zero when absent. -/
def coefficientOf (index : Nat) (linear : Linear) : Int :=
  Sparse.valueAtSize linear.coefficients index

/-- Delete the selected variable from a linear form. -/
def deleteVariable (index : Nat) (linear : Linear) : Linear :=
  ⟨linear.coefficients.filter (fun entry => decide (entry.1 ≠ index)), linear.offset⟩

/-- Detect presence in the source's finite coefficient map. -/
def mentions (index : Nat) (linear : Linear) : Bool :=
  linear.coefficients.any fun entry => entry.1 == index

/-- Extract a lower or upper bound, or reject a non-unit coefficient. -/
def bound (index : Nat) (linear : Linear) : Except Unit (Sum Linear Linear) :=
  if coefficientOf index linear = 1 then .ok (.inl (scale (-1) (deleteVariable index linear)))
  else if coefficientOf index linear = -1 then .ok (.inr (deleteVariable index linear))
  else .error ()

/-- Deletion removes the variable from the form's support. -/
theorem delete_free (index : Nat) (linear : Linear) :
    PolynomialSupport.LinearFree index (deleteVariable index linear) := by
  intro entry member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Deletion preserves the canonical coefficient-map invariant. -/
theorem delete_valid (index : Nat) (linear : Linear) (valid : Valid linear) :
    Valid (deleteVariable index linear) :=
  ⟨valid.1.filter _, fun entry member => valid.2 entry (List.mem_filter.mp member).1⟩

/-- Scalar multiplication preserves the absence of a variable. -/
theorem scale_free (index : Nat) (factor : Int) (linear : Linear)
    (free : PolynomialSupport.LinearFree index linear) :
    PolynomialSupport.LinearFree index (scale factor linear) := by
  by_cases zero : factor = 0
  · simp [scale, zero, constant, PolynomialSupport.LinearFree]
  · simp only [scale, zero, ↓reduceIte]
    intro entry member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact free original present

/-- The selected coefficient and the deleted map partition the linear value. -/
theorem coefficients_decompose (assignment : Nat → Int) (index : Nat) (value : Int)
    (coefficients : List (Nat × Int)) :
    evalCoefficients (update assignment index value) coefficients =
      Sparse.coefficient coefficients index * value +
        evalCoefficients assignment (coefficients.filter fun entry => decide (entry.1 ≠ index)) := by
  induction coefficients with
  | nil => simp [evalCoefficients, Sparse.coefficient]
  | cons entry rest ih =>
    rcases entry with ⟨other, coefficient⟩
    by_cases same : other = index
    · subst other
      simp only [evalCoefficients, update, ↓reduceIte, Sparse.coefficient, List.filter_cons,
        ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ih]
      grind
    · simp only [evalCoefficients, update, same, ↓reduceIte, Sparse.coefficient, List.filter_cons,
        ne_eq, not_false_eq_true, decide_true, ih]
      grind

/-- The executable sparse lookup supplies the selected coefficient exactly. -/
theorem evaluate_decompose (assignment : Nat → Int) (index : Nat) (value : Int)
    (linear : Linear) (valid : Valid linear) :
    evaluate (update assignment index value) linear =
      coefficientOf index linear * value + evaluate assignment (deleteVariable index linear) := by
  unfold evaluate coefficientOf deleteVariable
  rw [Sparse.valueAtSize_correct linear.coefficients valid.1, coefficients_decompose]
  dsimp only
  exact Int.add_left_comm _ _ _

/-- The lower-bound case preserves the original integer inequality. -/
theorem lower_correct (assignment : Nat → Int) (index : Nat) (value : Int)
    (linear : Linear) (valid : Valid linear) (coefficient : coefficientOf index linear = 1) :
    (0 ≤ evaluate (update assignment index value) linear) ↔
      evaluate assignment (scale (-1) (deleteVariable index linear)) ≤ value := by
  rw [evaluate_decompose assignment index value linear valid, coefficient, evaluate_scale]
  omega

/-- The upper-bound case preserves the original integer inequality. -/
theorem upper_correct (assignment : Nat → Int) (index : Nat) (value : Int)
    (linear : Linear) (valid : Valid linear) (coefficient : coefficientOf index linear = -1) :
    (0 ≤ evaluate (update assignment index value) linear) ↔
      value ≤ evaluate assignment (deleteVariable index linear) := by
  rw [evaluate_decompose assignment index value linear valid, coefficient]
  omega

/-- Every successful extraction has exact inequality semantics. -/
theorem bound_correct (assignment : Nat → Int) (index : Nat) (linear : Linear)
    (result : Sum Linear Linear) (valid : Valid linear) (success : bound index linear = .ok result)
    (value : Int) :
    (0 ≤ evaluate (update assignment index value) linear) ↔
      match result with
      | .inl lower => evaluate assignment lower ≤ value
      | .inr upper => value ≤ evaluate assignment upper := by
  unfold bound at success
  split at success
  · next coefficient =>
    cases success
    exact lower_correct assignment index value linear valid coefficient
  · split at success
    · next coefficient =>
      cases success
      exact upper_correct assignment index value linear valid coefficient
    · cases success

/-- Extracted bounds no longer contain the removed variable. -/
theorem bound_free (index : Nat) (linear : Linear) (result : Sum Linear Linear)
    (success : bound index linear = .ok result) :
    match result with
    | .inl lower => PolynomialSupport.LinearFree index lower
    | .inr upper => PolynomialSupport.LinearFree index upper := by
  unfold bound at success
  split at success
  · cases success; exact scale_free index (-1) _ (delete_free index linear)
  · split at success
    · cases success; exact delete_free index linear
    · cases success

/-- Extracted bounds preserve the canonical sparse-map representation. -/
theorem bound_valid (index : Nat) (linear : Linear) (result : Sum Linear Linear)
    (valid : Valid linear) (success : bound index linear = .ok result) :
    match result with
    | .inl lower => Valid lower
    | .inr upper => Valid upper := by
  unfold bound at success
  split at success
  · cases success; exact scale_valid (-1) _ (delete_valid index linear valid)
  · split at success
    · cases success; exact delete_valid index linear valid
    · cases success

/-- A form excluded by `mentions` has no dependence on the selected variable. -/
theorem mentions_false_free (index : Nat) (linear : Linear) (absent : mentions index linear = false) :
    PolynomialSupport.LinearFree index linear := by
  intro entry member same
  have present : mentions index linear = true := by
    apply List.any_eq_true.mpr
    exact ⟨entry, member, by simpa using same⟩
  rw [absent] at present
  contradiction

/-- Assigning an absent variable does not change a linear form's value. -/
theorem evaluate_free (assignment : Nat → Int) (index : Nat) (value : Int)
    (linear : Linear) (free : PolynomialSupport.LinearFree index linear) :
    evaluate (update assignment index value) linear = evaluate assignment linear := by
  unfold evaluate
  congr 1
  have go (coefficients : List (Nat × Int)) (allFree : ∀ entry ∈ coefficients, entry.1 ≠ index) :
      evalCoefficients (update assignment index value) coefficients = evalCoefficients assignment coefficients := by
    induction coefficients with
    | nil => rfl
    | cons entry rest ih =>
      have head := allFree entry (by simp)
      simp only [evalCoefficients, update, head, ↓reduceIte]
      rw [ih (fun item member => allFree item (by simp [member]))]
  exact go linear.coefficients free

/-- Integer updates agree with the rational update used by polynomial summation. -/
theorem update_rat_bridge (assignment : Nat → Int) (index : Nat) (value : Int) :
    (fun other => (update assignment index value other : Rat)) =
      PolynomialSum.update (fun other => (assignment other : Rat)) index (value : Rat) := by
  funext other
  by_cases same : other = index <;> simp [update, PolynomialSum.update, same]

end MicroCFTA.LatticeBound
