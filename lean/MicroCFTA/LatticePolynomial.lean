import Std

/-!
# Sparse polynomial arithmetic for integer-point counting

A polynomial is a finite list representation of a sparse map. Monomial keys
are finite exponent maps. Coefficient insertion combines equal keys and
removes zero coefficients, as the Haskell map operations do.

Exponents are natural numbers. The Haskell representation uses `Int`, but its
constructors produce nonnegative exponents. This file does not verify the
balanced-tree map implementation or the Faulhaber coefficient construction.
-/

namespace MicroCFTA.LatticePolynomial

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩
local instance : Std.Associative (α := Rat) (· + ·) := ⟨Rat.add_assoc⟩
local instance : Std.Commutative (α := Rat) (· + ·) := ⟨Rat.add_comm⟩

/-- A variable index. -/
abbrev Variable := Nat

/-- A finite list representation of an exponent map. -/
abbrev Monomial := List (Variable × Nat)

/-- A sparse polynomial with rational coefficients. -/
abbrev Polynomial := List (Monomial × Rat)

/-- Evaluate a monomial at a rational assignment. -/
def evalMonomial (assignment : Variable → Rat) : Monomial → Rat
  | [] => 1
  | (index, power) :: rest => assignment index ^ power * evalMonomial assignment rest

/-- Interpret each monomial independently and sum its coefficient. -/
def interpret (monomialValue : Monomial → Rat) : Polynomial → Rat
  | [] => 0
  | (monomial, coefficient) :: rest => coefficient * monomialValue monomial + interpret monomialValue rest

/-- Evaluate a polynomial at a rational assignment. -/
def evaluate (assignment : Variable → Rat) : Polynomial → Rat := interpret (evalMonomial assignment)

/-- Natural powers turn exponent addition into multiplication. -/
theorem rat_pow_add (value : Rat) (left right : Nat) :
    value ^ (left + right) = value ^ left * value ^ right := by
  induction right with
  | zero => simp
  | succ right ih => rw [Nat.add_succ, Rat.pow_succ, Rat.pow_succ, ih, Rat.mul_assoc]

/-- Insert an exponent into an ordered finite exponent map, adding on collision. -/
def insertPower (index power : Nat) : Monomial → Monomial
  | [] => [(index, power)]
  | (other, oldPower) :: rest =>
      if index < other then (index, power) :: (other, oldPower) :: rest
      else if index = other then (other, power + oldPower) :: rest
      else (other, oldPower) :: insertPower index power rest

/-- Exponent insertion multiplies by precisely the inserted variable power. -/
theorem eval_insertPower (assignment : Variable → Rat) (index power : Nat) (monomial : Monomial) :
    evalMonomial assignment (insertPower index power monomial) =
      assignment index ^ power * evalMonomial assignment monomial := by
  induction monomial with
  | nil => simp [insertPower, evalMonomial]
  | cons entry rest ih =>
      rcases entry with ⟨other, oldPower⟩
      simp only [insertPower]
      split
      · rfl
      · split
        · next same => subst other; simp [evalMonomial, rat_pow_add, Rat.mul_assoc]
        · simp only [evalMonomial, ih]
          ac_rfl

/-- Union exponent maps by adding the exponents of each shared index. -/
def multiplyMonomials (left right : Monomial) : Monomial :=
  left.foldr (fun (index, power) rest => insertPower index power rest) right

/-- Monomial multiplication evaluates to the product of the two values. -/
theorem eval_multiplyMonomials (assignment : Variable → Rat) (left right : Monomial) :
    evalMonomial assignment (multiplyMonomials left right) =
      evalMonomial assignment left * evalMonomial assignment right := by
  induction left with
  | nil => simp [multiplyMonomials, evalMonomial]
  | cons entry rest ih =>
      rcases entry with ⟨index, power⟩
      change evalMonomial assignment (insertPower index power (multiplyMonomials rest right)) = _
      rw [eval_insertPower, ih]
      simp [evalMonomial, Rat.mul_assoc]

/-- Insert a sparse coefficient, add equal keys, and remove a zero sum. -/
def insertCoefficient (monomial : Monomial) (coefficient : Rat) : Polynomial → Polynomial
  | [] => if coefficient = 0 then [] else [(monomial, coefficient)]
  | (other, oldCoefficient) :: rest =>
      if monomial = other then
        if coefficient + oldCoefficient = 0 then rest else (other, coefficient + oldCoefficient) :: rest
      else (other, oldCoefficient) :: insertCoefficient monomial coefficient rest

/-- Sparse coefficient insertion adds exactly the supplied monomial contribution. -/
theorem interpret_insertCoefficient (value : Monomial → Rat) (monomial : Monomial)
    (coefficient : Rat) (polynomial : Polynomial) :
    interpret value (insertCoefficient monomial coefficient polynomial) =
      coefficient * value monomial + interpret value polynomial := by
  induction polynomial with
  | nil =>
      simp only [insertCoefficient]
      split <;> simp_all [interpret, Rat.add_zero]
  | cons entry rest ih =>
      rcases entry with ⟨other, oldCoefficient⟩
      simp only [insertCoefficient]
      split
      · next same =>
          subst other
          split
          · next zero =>
              simp only [interpret]
              rw [← Rat.add_assoc, ← Rat.add_mul, zero]
              simp [Rat.zero_add]
          · simp only [interpret, Rat.add_mul]
            ac_rfl
      · simp only [interpret, ih]
        ac_rfl

/-- Normalize the finite sparse map representation. -/
def normalize (polynomial : Polynomial) : Polynomial :=
  polynomial.foldr (fun (monomial, coefficient) rest => insertCoefficient monomial coefficient rest) []

/-- Combining equal monomials and dropping zeros preserves every interpretation. -/
theorem interpret_normalize (value : Monomial → Rat) (polynomial : Polynomial) :
    interpret value (normalize polynomial) = interpret value polynomial := by
  induction polynomial with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨monomial, coefficient⟩
      change interpret value (insertCoefficient monomial coefficient (normalize rest)) = _
      rw [interpret_insertCoefficient, ih]
      rfl

/-- Concatenating coefficient entries adds their values. -/
theorem interpret_append (value : Monomial → Rat) (left right : Polynomial) :
    interpret value (left ++ right) = interpret value left + interpret value right := by
  induction left with
  | nil => simp [interpret, Rat.zero_add]
  | cons entry rest ih => cases entry; simp [interpret, ih, Rat.add_assoc]

/-- Sparse constant construction, with zero removed. -/
def polynomialConstant (value : Rat) : Polynomial := normalize [([], value)]

/-- Constant construction has the specified value at every assignment. -/
theorem evaluate_constant (assignment : Variable → Rat) (value : Rat) :
    evaluate assignment (polynomialConstant value) = value := by
  simp [evaluate, polynomialConstant, interpret_normalize, interpret, evalMonomial, Rat.add_zero]

/-- Sparse polynomial addition. -/
def addPolynomials (left right : Polynomial) : Polynomial := normalize (left ++ right)

/-- Polynomial addition is exact. -/
theorem evaluate_add (assignment : Variable → Rat) (left right : Polynomial) :
    evaluate assignment (addPolynomials left right) = evaluate assignment left + evaluate assignment right := by
  exact (interpret_normalize _ _).trans (interpret_append _ _ _)

/-- The Cartesian coefficient product before equal monomials are combined. -/
def rawProduct (left right : Polynomial) : Polynomial :=
  left.flatMap fun (leftMonomial, leftCoefficient) =>
    right.map fun (rightMonomial, rightCoefficient) =>
      (multiplyMonomials leftMonomial rightMonomial, leftCoefficient * rightCoefficient)

/-- Sparse polynomial multiplication. -/
def multiplyPolynomials (left right : Polynomial) : Polynomial := normalize (rawProduct left right)

/-- Multiplying by one monomial distributes across the entire coefficient map. -/
theorem evaluate_product_row (assignment : Variable → Rat) (monomial : Monomial) (coefficient : Rat)
    (polynomial : Polynomial) :
    evaluate assignment (polynomial.map fun (other, weight) =>
      (multiplyMonomials monomial other, coefficient * weight)) =
      coefficient * evalMonomial assignment monomial * evaluate assignment polynomial := by
  induction polynomial with
  | nil => simp [evaluate, interpret]
  | cons entry rest ih =>
      rcases entry with ⟨other, weight⟩
      simp only [List.map_cons, evaluate, interpret] at *
      rw [eval_multiplyMonomials, ih, Rat.mul_add]
      congr 1
      ac_rfl

/-- The Cartesian product evaluates as multiplication before normalization. -/
theorem evaluate_rawProduct (assignment : Variable → Rat) (left right : Polynomial) :
    evaluate assignment (rawProduct left right) = evaluate assignment left * evaluate assignment right := by
  induction left with
  | nil => simp [rawProduct, evaluate, interpret]
  | cons entry rest ih =>
      rcases entry with ⟨monomial, coefficient⟩
      change evaluate assignment ((right.map fun (other, weight) =>
        (multiplyMonomials monomial other, coefficient * weight)) ++ rawProduct rest right) = _
      rw [show evaluate assignment (_ ++ _) = evaluate assignment _ + evaluate assignment _ from interpret_append _ _ _,
        evaluate_product_row, ih]
      simp [evaluate, interpret, Rat.add_mul]

/-- Sparse multiplication is exact, including cancellation between equal monomials. -/
theorem evaluate_multiply (assignment : Variable → Rat) (left right : Polynomial) :
    evaluate assignment (multiplyPolynomials left right) = evaluate assignment left * evaluate assignment right := by
  exact (interpret_normalize _ _).trans (evaluate_rawProduct _ _ _)

/-- Values substituted for some of the integer variables. -/
abbrev Substitution := Variable → Option Int

/-- Remove every index supplied by the substitution. -/
def remaining (values : Substitution) (monomial : Monomial) : Monomial :=
  monomial.filter fun (index, _) => (values index).isNone

/-- Multiply the powers of all assigned integer variables. -/
def assignedFactor (values : Substitution) : Monomial → Rat
  | [] => 1
  | (index, power) :: rest =>
      (match values index with
       | none => 1
       | some value => (value : Rat) ^ power) * assignedFactor values rest

/-- A substitution overrides the variables for which it supplies a value. -/
def override (values : Substitution) (assignment : Variable → Rat) : Variable → Rat :=
  fun index => match values index with
    | none => assignment index
    | some value => value

/-- Deleting assigned variables and multiplying their powers preserves monomial evaluation. -/
theorem eval_substituted_monomial (values : Substitution) (assignment : Variable → Rat) (monomial : Monomial) :
    assignedFactor values monomial * evalMonomial assignment (remaining values monomial) =
      evalMonomial (override values assignment) monomial := by
  induction monomial with
  | nil => simp [assignedFactor, remaining, evalMonomial]
  | cons entry rest ih =>
      rcases entry with ⟨index, power⟩
      cases found : values index with
      | none =>
          simp only [remaining, List.filter_cons, found, Option.isNone_none, ↓reduceIte,
            assignedFactor, Rat.one_mul, evalMonomial, override]
          change assignedFactor values rest * (assignment index ^ power * evalMonomial assignment (remaining values rest)) = _
          calc
            _ = assignment index ^ power * (assignedFactor values rest * evalMonomial assignment (remaining values rest)) := by ac_rfl
            _ = _ := by rw [ih]
      | some value =>
          simp only [remaining, List.filter_cons, found, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
            assignedFactor, evalMonomial, override]
          change ((value : Rat) ^ power * assignedFactor values rest) * evalMonomial assignment (remaining values rest) = _
          rw [Rat.mul_assoc, ih]

/-- Replace assigned variables and combine the remaining monomials. -/
def substitute (values : Substitution) (polynomial : Polynomial) : Polynomial :=
  normalize (polynomial.map fun (monomial, coefficient) =>
    (remaining values monomial, coefficient * assignedFactor values monomial))

/-- Partial integer substitution agrees with evaluating the original at the overridden assignment. -/
theorem evaluate_substitute (values : Substitution) (assignment : Variable → Rat) (polynomial : Polynomial) :
    evaluate assignment (substitute values polynomial) = evaluate (override values assignment) polynomial := by
  unfold substitute evaluate
  rw [interpret_normalize]
  induction polynomial with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨monomial, coefficient⟩
      simp only [List.map_cons, interpret]
      rw [ih, Rat.mul_assoc, eval_substituted_monomial]

/-- Successive substitutions have the correct first-assignment precedence. -/
theorem evaluate_substitute_twice (first second : Substitution) (assignment : Variable → Rat)
    (polynomial : Polynomial) :
    evaluate assignment (substitute second (substitute first polynomial)) =
      evaluate (override first (override second assignment)) polynomial := by
  rw [evaluate_substitute, evaluate_substitute]

/-- A finite integer linear form. -/
structure Linear where
  coefficients : List (Variable × Int)
  offset : Int

/-- Evaluate the integer coefficients of a linear form at a rational assignment. -/
def evaluateLinearTerms (assignment : Variable → Rat) : List (Variable × Int) → Rat
  | [] => 0
  | (index, coefficient) :: rest => (coefficient : Rat) * assignment index + evaluateLinearTerms assignment rest

/-- Include the linear form's constant offset. -/
def evaluateLinear (assignment : Variable → Rat) (linear : Linear) : Rat :=
  (linear.offset : Rat) + evaluateLinearTerms assignment linear.coefficients

/-- Convert one linear form to its constant and degree-one monomials. -/
def fromLinear (linear : Linear) : Polynomial :=
  normalize (([], (linear.offset : Rat)) :: linear.coefficients.map fun (index, coefficient) =>
    ([(index, 1)], (coefficient : Rat)))

/-- Linear conversion preserves the form's value, including negative coefficients. -/
theorem evaluate_fromLinear (assignment : Variable → Rat) (linear : Linear) :
    evaluate assignment (fromLinear linear) = evaluateLinear assignment linear := by
  unfold evaluate fromLinear
  rw [interpret_normalize]
  simp only [interpret, evalMonomial, Rat.mul_one, evaluateLinear]
  congr 1
  induction linear.coefficients with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨index, coefficient⟩
      simp [List.map_cons, interpret, evalMonomial, evaluateLinearTerms, ih]

/-- Sparse polynomial entries have distinct monomial keys. -/
def UniqueMonomials (polynomial : Polynomial) : Prop :=
  polynomial.Pairwise (fun left right => left.1 ≠ right.1)

/-- Insertion introduces only its supplied key and keys already in the map. -/
theorem insertCoefficient_keys (monomial : Monomial) (coefficient : Rat) (polynomial : Polynomial)
    (entry : Monomial × Rat) (member : entry ∈ insertCoefficient monomial coefficient polynomial) :
    entry.1 = monomial ∨ ∃ old, (entry.1, old) ∈ polynomial := by
  induction polynomial with
  | nil =>
      simp only [insertCoefficient] at member
      split at member
      · contradiction
      · have same := List.mem_singleton.mp member
        cases same
        exact Or.inl rfl
  | cons head rest ih =>
      rcases head with ⟨other, oldCoefficient⟩
      simp only [insertCoefficient] at member
      split at member
      · next same =>
          split at member
          · exact Or.inr ⟨entry.2, List.mem_cons_of_mem _ member⟩
          · rcases List.mem_cons.mp member with equal | member
            · cases equal
              exact Or.inl same.symm
            · exact Or.inr ⟨entry.2, List.mem_cons_of_mem _ member⟩
      · rcases List.mem_cons.mp member with equal | member
        · cases equal
          exact Or.inr ⟨oldCoefficient, by simp⟩
        · rcases ih member with inserted | ⟨old, member⟩
          · exact Or.inl inserted
          · exact Or.inr ⟨old, List.mem_cons_of_mem _ member⟩

/-- Coefficient insertion preserves unique sparse-map keys. -/
theorem insertCoefficient_unique (monomial : Monomial) (coefficient : Rat) (polynomial : Polynomial)
    (unique : UniqueMonomials polynomial) : UniqueMonomials (insertCoefficient monomial coefficient polynomial) := by
  induction polynomial with
  | nil =>
      simp only [insertCoefficient]
      split <;> simp [UniqueMonomials]
  | cons head rest ih =>
      rcases head with ⟨other, oldCoefficient⟩
      obtain ⟨apart, tailUnique⟩ := List.pairwise_cons.mp unique
      simp only [insertCoefficient]
      split
      · split
        · exact tailUnique
        · exact List.pairwise_cons.mpr ⟨apart, tailUnique⟩
      · next different =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih tailUnique⟩
          intro entry member equal
          rcases insertCoefficient_keys monomial coefficient rest entry member with inserted | ⟨old, original⟩
          · exact different (equal.trans inserted).symm
          · exact apart (entry.1, old) original equal

/-- Normalization produces a map with one coefficient per monomial key. -/
theorem normalize_unique (polynomial : Polynomial) : UniqueMonomials (normalize polynomial) := by
  induction polynomial with
  | nil => exact List.Pairwise.nil
  | cons entry rest ih =>
      exact insertCoefficient_unique entry.1 entry.2 (normalize rest) ih

/-- Insertion removes a zero coefficient and preserves nonzero stored entries. -/
theorem insertCoefficient_nonzero (monomial : Monomial) (coefficient : Rat) (polynomial : Polynomial)
    (nonzero : ∀ entry ∈ polynomial, entry.2 ≠ 0) :
    ∀ entry ∈ insertCoefficient monomial coefficient polynomial, entry.2 ≠ 0 := by
  induction polynomial with
  | nil =>
      intro entry member
      simp only [insertCoefficient] at member
      split at member
      · contradiction
      · next hn =>
          have same := List.mem_singleton.mp member
          cases same
          exact hn
  | cons head rest ih =>
      rcases head with ⟨other, oldCoefficient⟩
      intro entry member
      have tailNonzero : ∀ entry ∈ rest, entry.2 ≠ 0 :=
        fun entry hm => nonzero entry (List.mem_cons_of_mem _ hm)
      simp only [insertCoefficient] at member
      split at member
      · split at member
        · exact tailNonzero entry member
        · next hn =>
            rcases List.mem_cons.mp member with same | member
            · cases same; exact hn
            · exact tailNonzero entry member
      · rcases List.mem_cons.mp member with same | member
        · cases same; exact nonzero (other, oldCoefficient) (by simp)
        · exact ih tailNonzero entry member

/-- Normalization stores no zero coefficient. -/
theorem normalize_nonzero (polynomial : Polynomial) :
    ∀ entry ∈ normalize polynomial, entry.2 ≠ 0 := by
  induction polynomial with
  | nil => simp [normalize]
  | cons entry rest ih => exact insertCoefficient_nonzero entry.1 entry.2 (normalize rest) ih

/-- Read one coefficient from the finite sparse map. Missing keys have coefficient zero. -/
def coefficientAt (monomial : Monomial) : Polynomial → Rat
  | [] => 0
  | (other, coefficient) :: rest => if monomial = other then coefficient else coefficientAt monomial rest

/-- Interpret one key as one and every other key as zero. -/
def keyIndicator (wanted monomial : Monomial) : Rat := if wanted = monomial then 1 else 0

/-- Keys absent from every entry have zero aggregate coefficient. -/
theorem interpret_absent_key (wanted : Monomial) (polynomial : Polynomial)
    (absent : ∀ entry ∈ polynomial, wanted ≠ entry.1) : interpret (keyIndicator wanted) polynomial = 0 := by
  induction polynomial with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨monomial, coefficient⟩
      have head := absent (monomial, coefficient) (by simp)
      simp [interpret, keyIndicator, head,
        ih (fun entry hm => absent entry (List.mem_cons_of_mem _ hm)), Rat.zero_add]

/-- Sparse-map lookup equals aggregation when monomial keys are unique. -/
theorem coefficientAt_eq_interpret (wanted : Monomial) (polynomial : Polynomial)
    (unique : UniqueMonomials polynomial) :
    coefficientAt wanted polynomial = interpret (keyIndicator wanted) polynomial := by
  induction polynomial with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨monomial, coefficient⟩
      obtain ⟨apart, tailUnique⟩ := List.pairwise_cons.mp unique
      by_cases same : wanted = monomial
      · subst wanted
        have hz := interpret_absent_key monomial rest (fun entry hm => apart entry hm)
        simp [coefficientAt, interpret, keyIndicator, hz, Rat.add_zero]
      · simp [coefficientAt, interpret, keyIndicator, same, ih tailUnique, Rat.zero_add]

/-- Normalized map lookup returns the sum of all original coefficients at that key. -/
theorem coefficientAt_normalize (wanted : Monomial) (polynomial : Polynomial) :
    coefficientAt wanted (normalize polynomial) = interpret (keyIndicator wanted) polynomial := by
  rw [coefficientAt_eq_interpret wanted _ (normalize_unique polynomial), interpret_normalize]

/-- The constant coefficient read by `polynomialValue`. -/
def polynomialValue (polynomial : Polynomial) : Rat := coefficientAt [] polynomial

/-- Interpretation only depends on the keys that occur in the polynomial. -/
theorem interpret_congr (left right : Monomial → Rat) (polynomial : Polynomial)
    (same : ∀ entry ∈ polynomial, left entry.1 = right entry.1) :
    interpret left polynomial = interpret right polynomial := by
  induction polynomial with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨monomial, coefficient⟩
      rw [interpret, interpret, same (monomial, coefficient) (by simp),
        ih (fun entry hm => same entry (List.mem_cons_of_mem _ hm))]

/-- A monomial has no remaining variables when all its indices are assigned. -/
theorem remaining_empty (values : Substitution) (monomial : Monomial)
    (assigned : ∀ entry ∈ monomial, ∃ value, values entry.1 = some value) : remaining values monomial = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry member
  obtain ⟨value, found⟩ := assigned entry member
  simp [found]

/-- Fully assigning a polynomial makes its constant coefficient equal its complete value. -/
theorem polynomialValue_substitute (values : Substitution) (assignment : Variable → Rat) (polynomial : Polynomial)
    (assigned : ∀ entry ∈ polynomial, ∀ power ∈ entry.1, ∃ value, values power.1 = some value) :
    polynomialValue (substitute values polynomial) = evaluate (override values assignment) polynomial := by
  have hc : interpret (keyIndicator [])
      (polynomial.map fun (monomial, coefficient) =>
        (remaining values monomial, coefficient * assignedFactor values monomial)) =
      interpret (evalMonomial assignment)
      (polynomial.map fun (monomial, coefficient) =>
        (remaining values monomial, coefficient * assignedFactor values monomial)) := by
    apply interpret_congr
    intro entry member
    obtain ⟨⟨monomial, coefficient⟩, original, rfl⟩ := List.mem_map.mp member
    have empty := remaining_empty values monomial (assigned (monomial, coefficient) original)
    simp [empty, keyIndicator, evalMonomial]
  calc
    polynomialValue (substitute values polynomial) = _ := coefficientAt_normalize [] _
    _ = _ := hc
    _ = evaluate assignment (substitute values polynomial) := (interpret_normalize _ _).symm
    _ = _ := evaluate_substitute values assignment polynomial

/-- Total integer substitution verifies the constant-extraction step without an external premise. -/
theorem polynomialValue_substituteAll (assignment : Variable → Int) (polynomial : Polynomial) :
    polynomialValue (substitute (fun index => some (assignment index)) polynomial) =
      evaluate (fun index => (assignment index : Rat)) polynomial := by
  exact polynomialValue_substitute (fun index => some (assignment index)) (fun _ => 0) polynomial
    (by intro entry member power memberPower; exact ⟨assignment power.1, rfl⟩)

/-- Exponent maps store variable indices in strict ascending order. -/
def OrderedMonomial (monomial : Monomial) : Prop :=
  monomial.Pairwise (fun left right => left.1 < right.1)

/-- Exponent insertion introduces only the inserted index and existing indices. -/
theorem insertPower_indices (index power : Nat) (monomial : Monomial)
    (entry : Variable × Nat) (member : entry ∈ insertPower index power monomial) :
    entry.1 = index ∨ ∃ oldPower, (entry.1, oldPower) ∈ monomial := by
  induction monomial with
  | nil =>
      have same := List.mem_singleton.mp member
      cases same
      exact Or.inl rfl
  | cons head rest ih =>
      rcases head with ⟨other, oldPower⟩
      simp only [insertPower] at member
      split at member
      · rcases List.mem_cons.mp member with same | member
        · cases same; exact Or.inl rfl
        · exact Or.inr ⟨entry.2, member⟩
      · split at member
        · next same =>
            rcases List.mem_cons.mp member with equal | member
            · cases equal; exact Or.inl same.symm
            · exact Or.inr ⟨entry.2, List.mem_cons_of_mem _ member⟩
        · rcases List.mem_cons.mp member with equal | member
          · cases equal; exact Or.inr ⟨oldPower, by simp⟩
          · rcases ih member with inserted | ⟨old, original⟩
            · exact Or.inl inserted
            · exact Or.inr ⟨old, List.mem_cons_of_mem _ original⟩

/-- Exponent insertion preserves a strict lower bound on every stored index. -/
theorem insertPower_above (low index power : Nat) (monomial : Monomial)
    (hi : low < index) (hm : ∀ entry ∈ monomial, low < entry.1) :
    ∀ entry ∈ insertPower index power monomial, low < entry.1 := by
  intro entry member
  rcases insertPower_indices index power monomial entry member with inserted | ⟨old, original⟩
  · simpa [inserted] using hi
  · exact hm (entry.1, old) original

/-- Sorted exponent maps remain sorted after insertion and collision addition. -/
theorem insertPower_ordered (index power : Nat) (monomial : Monomial)
    (ordered : OrderedMonomial monomial) : OrderedMonomial (insertPower index power monomial) := by
  induction monomial with
  | nil => simp [insertPower, OrderedMonomial]
  | cons head rest ih =>
      rcases head with ⟨other, oldPower⟩
      obtain ⟨above, tailOrdered⟩ := List.pairwise_cons.mp ordered
      simp only [insertPower]
      split
      · next before =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, ordered⟩
          intro entry member
          rcases List.mem_cons.mp member with same | member
          · cases same; exact before
          · exact Nat.lt_trans before (above entry member)
      · split
        · exact List.pairwise_cons.mpr ⟨above, tailOrdered⟩
        · next different =>
            apply List.pairwise_cons.mpr
            exact ⟨insertPower_above other index power rest (by omega) above, ih tailOrdered⟩

/-- Merging exponent maps preserves their finite-map representation. -/
theorem multiplyMonomials_ordered (left right : Monomial) (ordered : OrderedMonomial right) :
    OrderedMonomial (multiplyMonomials left right) := by
  induction left with
  | nil => exact ordered
  | cons entry rest ih => exact insertPower_ordered entry.1 entry.2 _ ih

/-- All monomial keys of a sparse polynomial are ordered exponent maps. -/
def OrderedMonomials (polynomial : Polynomial) : Prop :=
  ∀ entry ∈ polynomial, OrderedMonomial entry.1

/-- Coefficient insertion does not alter any exponent map. -/
theorem insertCoefficient_ordered (monomial : Monomial) (coefficient : Rat) (polynomial : Polynomial)
    (hm : OrderedMonomial monomial) (hp : OrderedMonomials polynomial) :
    OrderedMonomials (insertCoefficient monomial coefficient polynomial) := by
  intro entry member
  rcases insertCoefficient_keys monomial coefficient polynomial entry member with same | ⟨old, original⟩
  · simpa [same] using hm
  · exact hp (entry.1, old) original

/-- Sparse normalization preserves all exponent-map invariants. -/
theorem normalize_ordered (polynomial : Polynomial) (ordered : OrderedMonomials polynomial) :
    OrderedMonomials (normalize polynomial) := by
  induction polynomial with
  | nil => simp [OrderedMonomials, normalize]
  | cons entry rest ih =>
      exact insertCoefficient_ordered entry.1 entry.2 _ (ordered entry (by simp))
        (ih (fun entry member => ordered entry (List.mem_cons_of_mem _ member)))

/-- Linear conversion produces valid ordered exponent maps. -/
theorem fromLinear_ordered (linear : Linear) : OrderedMonomials (fromLinear linear) := by
  apply normalize_ordered
  intro entry member
  rcases List.mem_cons.mp member with same | member
  · cases same; exact List.Pairwise.nil
  · obtain ⟨⟨index, coefficient⟩, original, rfl⟩ := List.mem_map.mp member
    simp [OrderedMonomial]

/-- Sparse addition preserves the representation invariant. -/
theorem addPolynomials_ordered (left right : Polynomial)
    (hl : OrderedMonomials left) (hr : OrderedMonomials right) :
    OrderedMonomials (addPolynomials left right) := by
  apply normalize_ordered
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact hl entry member
  · exact hr entry member

/-- Sparse multiplication preserves ordered exponent maps. -/
theorem multiplyPolynomials_ordered (left right : Polynomial) (hr : OrderedMonomials right) :
    OrderedMonomials (multiplyPolynomials left right) := by
  apply normalize_ordered
  intro entry member
  obtain ⟨⟨lm, lc⟩, leftMember, rightMember⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨rm, rc⟩, original, rfl⟩ := List.mem_map.mp rightMember
  exact multiplyMonomials_ordered lm rm (hr (rm, rc) original)

/-- Deleting assigned variables preserves an ordered exponent map. -/
theorem remaining_ordered (values : Substitution) (monomial : Monomial) (ordered : OrderedMonomial monomial) :
    OrderedMonomial (remaining values monomial) := by
  exact List.Pairwise.filter _ ordered

/-- Partial substitution preserves the sparse-map representation. -/
theorem substitute_ordered (values : Substitution) (polynomial : Polynomial)
    (ordered : OrderedMonomials polynomial) : OrderedMonomials (substitute values polynomial) := by
  apply normalize_ordered
  intro entry member
  obtain ⟨⟨monomial, coefficient⟩, original, rfl⟩ := List.mem_map.mp member
  exact remaining_ordered values monomial (ordered (monomial, coefficient) original)

/-- Map enumeration order does not change a polynomial's interpretation. -/
theorem interpret_perm (value : Monomial → Rat) (left right : Polynomial) (permutation : left.Perm right) :
    interpret value left = interpret value right := by
  induction permutation with
  | nil => rfl
  | cons entry permutation ih => cases entry; simp [interpret, ih]
  | swap first second rest => cases first; cases second; simp [interpret, Rat.add_left_comm]
  | trans _ _ leftIH rightIH => exact leftIH.trans rightIH

/-- Build the repeated polynomial product used by Faulhaber's `powerOf`. -/
def polynomialPower (polynomial : Polynomial) (exponent : Nat) : Polynomial :=
  (List.replicate exponent polynomial).foldr multiplyPolynomials (polynomialConstant 1)

/-- The executable repeated product evaluates to the corresponding rational power. -/
theorem evaluate_power (assignment : Variable → Rat) (polynomial : Polynomial) (exponent : Nat) :
    evaluate assignment (polynomialPower polynomial exponent) = evaluate assignment polynomial ^ exponent := by
  induction exponent with
  | zero => simp [polynomialPower, evaluate_constant]
  | succ exponent ih =>
      change evaluate assignment (multiplyPolynomials polynomial (polynomialPower polynomial exponent)) = _
      rw [evaluate_multiply, ih, Rat.pow_succ, Rat.mul_comm]

/-- Add a finite list of polynomials, starting from the zero polynomial. -/
def sumPolynomials (polynomials : List Polynomial) : Polynomial :=
  polynomials.foldr addPolynomials (polynomialConstant 0)

/-- Finite polynomial summation is exact. -/
theorem evaluate_sum (assignment : Variable → Rat) (polynomials : List Polynomial) :
    evaluate assignment (sumPolynomials polynomials) = (polynomials.map (evaluate assignment)).sum := by
  induction polynomials with
  | nil => exact evaluate_constant assignment 0
  | cons polynomial rest ih =>
      change evaluate assignment (addPolynomials polynomial (sumPolynomials rest)) = _
      rw [evaluate_add, ih]
      rfl

/-- Form a finite weighted sum with the same operations used by `sumOver`. -/
def linearCombination (terms : List (Rat × Polynomial)) : Polynomial :=
  sumPolynomials (terms.map fun (coefficient, polynomial) =>
    multiplyPolynomials (polynomialConstant coefficient) polynomial)

/-- Coefficient-weighted polynomial assembly evaluates to the expected finite sum. -/
theorem evaluate_linearCombination (assignment : Variable → Rat) (terms : List (Rat × Polynomial)) :
    evaluate assignment (linearCombination terms) =
      (terms.map fun (coefficient, polynomial) => coefficient * evaluate assignment polynomial).sum := by
  rw [linearCombination, evaluate_sum]
  simp [List.map_map, Function.comp_def, evaluate_multiply, evaluate_constant]

/-- A checked cancellation and partial-substitution example. -/
theorem cancellation_example :
    normalize [([(0, 1)], 3), ([], 4), ([(0, 1)], -3)] = [([], 4)] ∧
      polynomialValue (substitute (fun index => if index = 0 then some (-2) else none)
        [([(0, 2)], 3), ([], -5)]) = 7 := by decide +kernel

end MicroCFTA.LatticePolynomial
