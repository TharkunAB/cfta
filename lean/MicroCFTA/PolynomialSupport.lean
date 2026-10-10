import MicroCFTA.PolynomialSum

/-!
# Variable support through polynomial elimination

These proofs track variables in finite exponent maps. They show that `sumOver`
removes its selected variable when the endpoint forms do not contain that
variable. They also show that later elimination preserves earlier removals.
-/

namespace MicroCFTA.PolynomialSupport

open LatticePolynomial

/-- A variable is absent from every entry of a monomial. -/
def MonomialFree (index : Nat) (monomial : Monomial) : Prop :=
  ∀ entry ∈ monomial, entry.1 ≠ index

/-- A variable is absent from every monomial of a polynomial. -/
def Free (index : Nat) (polynomial : Polynomial) : Prop :=
  ∀ entry ∈ polynomial, MonomialFree index entry.1

/-- A variable is absent from a linear form's coefficient map. -/
def LinearFree (index : Nat) (linear : Linear) : Prop :=
  ∀ entry ∈ linear.coefficients, entry.1 ≠ index

/-- Deletion removes the selected variable from a monomial. -/
theorem delete_free (index : Nat) (monomial : Monomial) :
    MonomialFree index (PolynomialSum.deleteVariable index monomial) := by
  intro entry member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Deletion preserves the absence of all other variables. -/
theorem delete_preserves_free (removed index : Nat) (monomial : Monomial)
    (free : MonomialFree index monomial) :
    MonomialFree index (PolynomialSum.deleteVariable removed monomial) := by
  intro entry member
  exact free entry (List.mem_filter.mp member).1

/-- Inserting another variable preserves absence. -/
theorem insertPower_free (index other power : Nat) (monomial : Monomial)
    (apart : other ≠ index) (free : MonomialFree index monomial) :
    MonomialFree index (insertPower other power monomial) := by
  intro entry member
  rcases insertPower_indices other power monomial entry member with same | original
  · exact same ▸ apart
  · obtain ⟨oldPower, original⟩ := original
    exact free (entry.1, oldPower) original

/-- Exponent-map multiplication cannot introduce an absent variable. -/
theorem multiplyMonomials_free (index : Nat) (left right : Monomial)
    (hl : MonomialFree index left) (hr : MonomialFree index right) :
    MonomialFree index (multiplyMonomials left right) := by
  induction left with
  | nil => exact hr
  | cons entry rest ih =>
    apply insertPower_free index entry.1 entry.2
    · exact hl entry (by simp)
    · exact ih (fun item member => hl item (by simp [member]))

/-- Inserting a coefficient keeps the supplied and existing variable support. -/
theorem insertCoefficient_free (index : Nat) (monomial : Monomial) (coefficient : Rat)
    (polynomial : Polynomial) (hm : MonomialFree index monomial) (hp : Free index polynomial) :
    Free index (insertCoefficient monomial coefficient polynomial) := by
  intro entry member
  rcases insertCoefficient_keys monomial coefficient polynomial entry member with same | original
  · simpa only [same] using hm
  · obtain ⟨old, member⟩ := original
    exact hp (entry.1, old) member

/-- Coefficient normalization does not add variable occurrences. -/
theorem normalize_free (index : Nat) (polynomial : Polynomial) (free : Free index polynomial) :
    Free index (normalize polynomial) := by
  induction polynomial with
  | nil => simp [Free, normalize]
  | cons entry rest ih =>
    exact insertCoefficient_free index entry.1 entry.2 _ (free entry (by simp))
      (ih (fun item member => free item (by simp [member])))

/-- A constant polynomial has no variable occurrences. -/
theorem constant_free (index : Nat) (value : Rat) : Free index (polynomialConstant value) := by
  apply normalize_free
  intro entry member
  obtain rfl := List.mem_singleton.mp member
  simp [MonomialFree]

/-- Sparse addition preserves absence. -/
theorem add_free (index : Nat) (left right : Polynomial) (hl : Free index left) (hr : Free index right) :
    Free index (addPolynomials left right) := by
  apply normalize_free
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact hl entry member
  · exact hr entry member

/-- Sparse multiplication preserves absence. -/
theorem multiply_free (index : Nat) (left right : Polynomial) (hl : Free index left) (hr : Free index right) :
    Free index (multiplyPolynomials left right) := by
  apply normalize_free
  intro entry member
  obtain ⟨⟨lm, lc⟩, lmMember, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨rm, rc⟩, rmMember, rfl⟩ := List.mem_map.mp mapped
  exact multiplyMonomials_free index lm rm (hl (lm, lc) lmMember) (hr (rm, rc) rmMember)

/-- Converting a linear form cannot add variables to its support. -/
theorem fromLinear_free (index : Nat) (linear : Linear) (free : LinearFree index linear) :
    Free index (fromLinear linear) := by
  apply normalize_free
  intro entry member
  rcases List.mem_cons.mp member with same | member
  · cases same; simp [MonomialFree]
  · obtain ⟨⟨other, coefficient⟩, original, rfl⟩ := List.mem_map.mp member
    intro item member
    obtain rfl := List.mem_singleton.mp member
    exact free (other, coefficient) original

/-- Polynomial powers preserve absence. -/
theorem power_free (index : Nat) (polynomial : Polynomial) (power : Nat) (free : Free index polynomial) :
    Free index (polynomialPower polynomial power) := by
  induction power with
  | zero => exact constant_free index 1
  | succ power ih => exact multiply_free index polynomial (polynomialPower polynomial power) free ih

/-- Finite polynomial sums preserve absence. -/
theorem sum_free (index : Nat) (polynomials : List Polynomial)
    (free : ∀ polynomial ∈ polynomials, Free index polynomial) : Free index (sumPolynomials polynomials) := by
  induction polynomials with
  | nil => exact constant_free index 0
  | cons polynomial rest ih =>
    exact add_free index polynomial (sumPolynomials rest) (free polynomial (by simp))
      (ih (fun item member => free item (by simp [member])))

/-- The Faulhaber construction has only variables from its polynomial argument. -/
theorem faulhaber_free (index power : Nat) (argument : Polynomial) (free : Free index argument) :
    Free index (Faulhaber.polynomialFaulhaber power argument) := by
  apply sum_free
  intro polynomial member
  obtain ⟨k, original, rfl⟩ := List.mem_map.mp member
  exact multiply_free index _ _ (constant_free index _) (power_free index argument _ free)

/-- Changing the constant offset does not change a linear form's variable support. -/
theorem predecessor_free (index : Nat) (linear : Linear) (free : LinearFree index linear) :
    LinearFree index (PolynomialSum.predecessor linear) := free

/-- The endpoint difference has only variables from the two bounds. -/
theorem powerSum_free (index power : Nat) (low high : Linear)
    (hl : LinearFree index low) (hh : LinearFree index high) :
    Free index (PolynomialSum.powerSum power low high) := by
  apply add_free
  · exact faulhaber_free _ _ _ (fromLinear_free index high hh)
  · exact multiply_free _ _ _ (constant_free index _)
      (faulhaber_free _ _ _ (fromLinear_free index _ (predecessor_free index low hl)))

/-- Summation deletes its variable when its bounds use only outer variables. -/
theorem sumOver_removes (index : Nat) (low high : Linear) (polynomial : Polynomial)
    (hl : LinearFree index low) (hh : LinearFree index high) :
    Free index (PolynomialSum.sumOver index low high polynomial) := by
  apply sum_free
  intro item member
  obtain ⟨entry, original, rfl⟩ := List.mem_map.mp member
  apply multiply_free
  · intro item member
    obtain rfl := List.mem_singleton.mp member
    exact delete_free index entry.1
  · exact powerSum_free index _ low high hl hh

/-- Later summation preserves each variable already removed from the input and bounds. -/
theorem sumOver_preserves_free (index removed : Nat) (low high : Linear) (polynomial : Polynomial)
    (hl : LinearFree index low) (hh : LinearFree index high) (hp : Free index polynomial) :
    Free index (PolynomialSum.sumOver removed low high polynomial) := by
  apply sum_free
  intro item member
  obtain ⟨entry, original, rfl⟩ := List.mem_map.mp member
  apply multiply_free
  · intro item member
    obtain rfl := List.mem_singleton.mp member
    exact delete_preserves_free removed index entry.1 (hp entry original)
  · exact powerSum_free index _ low high hl hh

/-- Evaluation is independent of an absent variable. -/
theorem evalMonomial_free (assignment : Nat → Rat) (index : Nat) (value : Rat)
    (monomial : Monomial) (free : MonomialFree index monomial) :
    evalMonomial (PolynomialSum.update assignment index value) monomial = evalMonomial assignment monomial := by
  induction monomial with
  | nil => rfl
  | cons entry rest ih =>
    have head := free entry (by simp)
    simp only [evalMonomial, PolynomialSum.update, head, ↓reduceIte]
    rw [ih (fun item member => free item (by simp [member]))]

/-- A polynomial does not change when an absent variable receives a value. -/
theorem evaluate_free (assignment : Nat → Rat) (index : Nat) (value : Rat)
    (polynomial : Polynomial) (free : Free index polynomial) :
    evaluate (PolynomialSum.update assignment index value) polynomial = evaluate assignment polynomial := by
  apply interpret_congr
  intro entry member
  exact evalMonomial_free assignment index value entry.1 (free entry member)

/-- A monomial with no variables is the empty exponent map. -/
theorem monomialFree_all (monomial : Monomial) (free : ∀ index, MonomialFree index monomial) : monomial = [] := by
  cases monomial with
  | nil => rfl
  | cons entry rest => exact False.elim (free entry.1 entry (by simp) rfl)

/-- After every variable is removed, sparse constant lookup equals evaluation. -/
theorem polynomialValue_free (assignment : Nat → Rat) (polynomial : Polynomial)
    (free : ∀ index, Free index polynomial) (unique : UniqueMonomials polynomial) :
    polynomialValue polynomial = evaluate assignment polynomial := by
  unfold polynomialValue evaluate
  rw [coefficientAt_eq_interpret [] polynomial unique]
  apply interpret_congr
  intro entry member
  have empty := monomialFree_all entry.1 (fun index => free index entry member)
  simp [empty, keyIndicator, evalMonomial]

/-- Finite polynomial summation always combines duplicate monomial keys. -/
theorem sum_unique (polynomials : List Polynomial) : UniqueMonomials (sumPolynomials polynomials) := by
  cases polynomials with
  | nil => exact normalize_unique [([], 0)]
  | cons polynomial rest => exact normalize_unique (polynomial ++ sumPolynomials rest)

/-- Each summation result has unique monomial keys for the final constant lookup. -/
theorem sumOver_unique (index : Nat) (low high : Linear) (polynomial : Polynomial) :
    UniqueMonomials (PolynomialSum.sumOver index low high polynomial) := sum_unique _

end MicroCFTA.PolynomialSupport
