import MicroCFTA.Faulhaber

/-!
# Exact summation of sparse polynomials

`sumOver` deletes the summed variable from each monomial and multiplies the
remaining monomial by the Faulhaber endpoint difference. The proofs use the
ordered exponent-map invariant. Bounds have their values at the fixed outer
assignment. The integer-point eliminator must separately prove that these
bounds do not depend on the variable it removes.
-/

namespace MicroCFTA.PolynomialSum

open LatticePolynomial

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩
local instance : Std.Associative (α := Rat) (· + ·) := ⟨Rat.add_assoc⟩
local instance : Std.Commutative (α := Rat) (· + ·) := ⟨Rat.add_comm⟩

/-- Replace one rational variable value. -/
def update (assignment : Nat → Rat) (index : Nat) (value : Rat) : Nat → Rat :=
  fun other => if other = index then value else assignment other

/-- Delete the selected variable from the finite exponent map. -/
def deleteVariable (index : Nat) (monomial : Monomial) : Monomial :=
  monomial.filter fun entry => decide (entry.1 ≠ index)

/-- Look up the exponent, with zero for an absent variable. -/
def exponentAt (index : Nat) : Monomial → Nat
  | [] => 0
  | (other, exponent) :: rest => if other = index then exponent else exponentAt index rest

/-- Sum repeated exponent entries. Ordered exponent maps have no repetitions. -/
def degree (index : Nat) : Monomial → Nat
  | [] => 0
  | (other, exponent) :: rest => (if other = index then exponent else 0) + degree index rest

/-- The degree of an absent variable is zero. -/
theorem degree_absent (index : Nat) (monomial : Monomial)
    (absent : ∀ entry ∈ monomial, entry.1 ≠ index) : degree index monomial = 0 := by
  induction monomial with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, exponent⟩
    have head := absent (other, exponent) (by simp)
    rw [degree, ite_eq_right_iff.mpr (fun h => False.elim (head h)), Nat.zero_add, ih (fun entry member => absent entry (by simp [member]))]

/-- Map lookup and total exponent coincide for the actual ordered representation. -/
theorem exponentAt_eq_degree (index : Nat) (monomial : Monomial)
    (ordered : OrderedMonomial monomial) : exponentAt index monomial = degree index monomial := by
  induction monomial with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, exponent⟩
    have pairwise := List.pairwise_cons.mp ordered
    by_cases same : other = index
    · subst other
      have absent : ∀ entry ∈ rest, entry.1 ≠ index := by
        intro entry member
        have before := pairwise.1 entry member
        change index < entry.1 at before
        exact Nat.ne_of_gt before
      simp [exponentAt, degree, degree_absent index rest absent]
    · simp [exponentAt, degree, same, ih pairwise.2]

/-- Factor the selected variable out of a monomial. -/
theorem evalMonomial_update_degree (assignment : Nat → Rat) (index : Nat) (value : Rat)
    (monomial : Monomial) :
    evalMonomial (update assignment index value) monomial =
      evalMonomial assignment (deleteVariable index monomial) * value ^ degree index monomial := by
  induction monomial with
  | nil => simp [evalMonomial, deleteVariable, degree]
  | cons entry rest ih =>
    rcases entry with ⟨other, exponent⟩
    by_cases same : other = index
    · subst other
      simp only [evalMonomial, update, ↓reduceIte, ih, deleteVariable, List.filter_cons,
        ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, degree]
      rw [rat_pow_add]
      ac_rfl
    · simp only [evalMonomial, update, same, ↓reduceIte, ih, deleteVariable, List.filter_cons,
        ne_eq, not_false_eq_true, decide_true, degree, Nat.zero_add]
      ac_rfl

/-- The factorization uses the source's default-zero lookup on ordered maps. -/
theorem evalMonomial_update (assignment : Nat → Rat) (index : Nat) (value : Rat)
    (monomial : Monomial) (ordered : OrderedMonomial monomial) :
    evalMonomial (update assignment index value) monomial =
      evalMonomial assignment (deleteVariable index monomial) * value ^ exponentAt index monomial := by
  rw [exponentAt_eq_degree index monomial ordered]
  exact evalMonomial_update_degree assignment index value monomial

/-- Equality at every integer input preserves a finite interval sum. -/
theorem intervalSum_congr (left right : Int → Rat) (same : ∀ value, left value = right value)
    (start : Int) (count : Nat) :
    Lattice.intervalSum left start count = Lattice.intervalSum right start count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Lattice.intervalSum, Lattice.intervalSum, ih, same]

/-- Finite interval sums distribute over rational addition. -/
theorem intervalSum_add (left right : Int → Rat) (start : Int) (count : Nat) :
    Lattice.intervalSum (fun value => left value + right value) start count =
      Lattice.intervalSum left start count + Lattice.intervalSum right start count := by
  induction count with
  | zero => simp [Lattice.intervalSum, Rat.add_zero]
  | succ count ih => simp only [Lattice.intervalSum, ih]; ac_rfl

/-- A fixed rational factor can leave a finite interval sum. -/
theorem intervalSum_mul (factor : Rat) (term : Int → Rat) (start : Int) (count : Nat) :
    Lattice.intervalSum (fun value => factor * term value) start count =
      factor * Lattice.intervalSum term start count := by
  induction count with
  | zero => simp [Lattice.intervalSum]
  | succ count ih => simp only [Lattice.intervalSum, ih, Rat.mul_add]

/-- Subtract one from a linear bound without changing its variable coefficients. -/
def predecessor (linear : Linear) : Linear := { linear with offset := linear.offset - 1 }

theorem evaluate_predecessor (assignment : Nat → Rat) (linear : Linear) :
    evaluateLinear assignment (predecessor linear) = evaluateLinear assignment linear - 1 := by
  simp only [evaluateLinear, predecessor, Rat.intCast_sub, Rat.intCast_one]
  grind

/-- The Faulhaber difference at two linear bounds. -/
def powerSum (power : Nat) (low high : Linear) : Polynomial :=
  addPolynomials (Faulhaber.polynomialFaulhaber power (fromLinear high))
    (multiplyPolynomials (polynomialConstant (-1))
      (Faulhaber.polynomialFaulhaber power
        (fromLinear (predecessor low))))

/-- The weighted monomial used by one entry of the source's `sumOver`. -/
def sumMonomial (index : Nat) (low high : Linear) (entry : Monomial × Rat) : Polynomial :=
  multiplyPolynomials [(deleteVariable index entry.1, entry.2)]
    (powerSum (exponentAt index entry.1) low high)

/-- Sum each sparse monomial and combine the resulting polynomials. -/
def sumOver (index : Nat) (low high : Linear) (polynomial : Polynomial) : Polynomial :=
  sumPolynomials (polynomial.map (sumMonomial index low high))

/-- The exact scalar value of the constructed endpoint difference. -/
theorem evaluate_powerSum (assignment : Nat → Rat) (power : Nat) (low high : Linear)
    (lowValue highValue : Int)
    (hl : evaluateLinear assignment low = (lowValue : Rat))
    (hh : evaluateLinear assignment high = (highValue : Rat))
    (ordered : lowValue ≤ highValue + 1) :
    evaluate assignment (powerSum power low high) =
      Lattice.intervalSum (fun value => (value : Rat) ^ power) lowValue (highValue - lowValue + 1).toNat := by
  unfold powerSum
  rw [evaluate_add, evaluate_multiply, evaluate_constant,
    Faulhaber.evaluate_polynomialFaulhaber, Faulhaber.evaluate_polynomialFaulhaber,
    evaluate_fromLinear, evaluate_fromLinear, evaluate_predecessor, hl, hh,
    Faulhaber.inclusive_power_sum power lowValue highValue ordered]
  have previous : ((lowValue - 1 : Int) : Rat) = (lowValue : Rat) - 1 := by
    rw [Rat.intCast_sub, Rat.intCast_one]
  rw [previous]
  grind

/-- Summing one sparse monomial preserves its exact value over the integer interval. -/
theorem evaluate_sumMonomial (assignment : Nat → Rat) (index : Nat) (low high : Linear)
    (entry : Monomial × Rat) (lowValue highValue : Int)
    (hl : evaluateLinear assignment low = (lowValue : Rat))
    (hh : evaluateLinear assignment high = (highValue : Rat))
    (interval : lowValue ≤ highValue + 1) (ordered : OrderedMonomial entry.1) :
    evaluate assignment (sumMonomial index low high entry) =
      Lattice.intervalSum
        (fun value => entry.2 * evalMonomial (update assignment index (value : Rat)) entry.1)
        lowValue (highValue - lowValue + 1).toNat := by
  unfold sumMonomial
  rw [evaluate_multiply, evaluate_powerSum assignment _ low high lowValue highValue hl hh interval]
  simp only [evaluate, interpret, Rat.add_zero]
  have terms : (fun value : Int => entry.2 * evalMonomial (update assignment index (value : Rat)) entry.1) =
      (fun value : Int => (entry.2 * evalMonomial assignment (deleteVariable index entry.1)) *
        (value : Rat) ^ exponentAt index entry.1) := by
    funext value
    rw [evalMonomial_update assignment index (value : Rat) entry.1 ordered, Rat.mul_assoc]
  rw [terms, intervalSum_mul]

/-- The complete sparse construction computes the original polynomial's finite sum. -/
theorem evaluate_sumOver (assignment : Nat → Rat) (index : Nat) (low high : Linear)
    (polynomial : Polynomial) (lowValue highValue : Int)
    (hl : evaluateLinear assignment low = (lowValue : Rat))
    (hh : evaluateLinear assignment high = (highValue : Rat))
    (interval : lowValue ≤ highValue + 1) (ordered : OrderedMonomials polynomial) :
    evaluate assignment (sumOver index low high polynomial) =
      Lattice.intervalSum (fun value => evaluate (update assignment index (value : Rat)) polynomial)
        lowValue (highValue - lowValue + 1).toNat := by
  induction polynomial with
  | nil =>
    simp only [sumOver, List.map_nil, sumPolynomials, List.foldr_nil, evaluate_constant]
    symm
    have zero : (fun value : Int => evaluate (update assignment index (value : Rat)) []) =
        fun _ => 0 := rfl
    rw [zero]
    induction (highValue - lowValue + 1).toNat with
    | zero => rfl
    | succ count ih => rw [Lattice.intervalSum, ih, Rat.add_zero]
  | cons entry rest ih =>
    have head : OrderedMonomial entry.1 := ordered entry (by simp)
    have tail : OrderedMonomials rest := fun item member => ordered item (by simp [member])
    change evaluate assignment (addPolynomials (sumMonomial index low high entry)
      (sumOver index low high rest)) = _
    rw [evaluate_add, evaluate_sumMonomial assignment index low high entry lowValue highValue hl hh interval head,
      ih tail]
    symm
    exact intervalSum_add _ _ _ _

/-- Constants satisfy the finite exponent-map ordering invariant. -/
theorem constant_ordered (value : Rat) : OrderedMonomials (polynomialConstant value) := by
  apply normalize_ordered
  intro entry member
  obtain rfl := List.mem_singleton.mp member
  exact List.Pairwise.nil

/-- A repeated product normalizes every monomial's exponent map. -/
theorem power_ordered (polynomial : Polynomial) (exponent : Nat) :
    OrderedMonomials (polynomialPower polynomial exponent) := by
  induction exponent with
  | zero => exact constant_ordered 1
  | succ exponent ih =>
    exact multiplyPolynomials_ordered polynomial (polynomialPower polynomial exponent) ih

/-- Summing valid polynomial maps keeps the exponent-map invariant. -/
theorem sum_ordered (polynomials : List Polynomial)
    (ordered : ∀ polynomial ∈ polynomials, OrderedMonomials polynomial) :
    OrderedMonomials (sumPolynomials polynomials) := by
  induction polynomials with
  | nil => exact constant_ordered 0
  | cons polynomial rest ih =>
    exact addPolynomials_ordered polynomial (sumPolynomials rest)
      (ordered polynomial (by simp))
      (ih (fun item member => ordered item (by simp [member])))

/-- The constructed Faulhaber polynomial has ordered exponent maps. -/
theorem faulhaber_ordered (power : Nat) (argument : Polynomial) :
    OrderedMonomials (Faulhaber.polynomialFaulhaber power argument) := by
  apply sum_ordered
  intro polynomial member
  obtain ⟨k, member, rfl⟩ := List.mem_map.mp member
  exact multiplyPolynomials_ordered _ _ (power_ordered argument (power + 1 - k))

/-- The endpoint difference has ordered exponent maps. -/
theorem powerSum_ordered (power : Nat) (low high : Linear) :
    OrderedMonomials (powerSum power low high) := by
  apply addPolynomials_ordered
  · exact faulhaber_ordered _ _
  · exact multiplyPolynomials_ordered _ _ (faulhaber_ordered _ _)

/-- One-variable summation preserves the input invariant required for later summation. -/
theorem sumOver_ordered (index : Nat) (low high : Linear) (polynomial : Polynomial) :
    OrderedMonomials (sumOver index low high polynomial) := by
  apply sum_ordered
  intro item member
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp member
  exact multiplyPolynomials_ordered _ _ (powerSum_ordered _ low high)

end MicroCFTA.PolynomialSum
