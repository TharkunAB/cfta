import MicroCFTA.LatticeInput

/-!
# Zero counts and integer implication decisions

The total of a nonnegative finite-support function is zero exactly when the
function is zero everywhere. Iterated elimination therefore decides emptiness
of a successfully compiled integer formula. Signed pieces can be negative;
the argument applies to their proved indicator-valued total.
-/

namespace MicroCFTA.LatticeDecision
open LatticeLinear LatticeSigned LatticeFormula LatticeInput LatticeCount

/-- A nonnegative finite list sum is zero exactly when every summand is zero. -/
theorem listSum_zero_iff (items : List α) (value : α → Rat) (nonnegative : ∀ item, 0 ≤ value item) :
    FiniteSum.listSum items value = 0 ↔ ∀ item ∈ items, value item = 0 := by
  induction items with
  | nil => simp [FiniteSum.listSum]
  | cons first rest ih =>
    have tailNonnegative : 0 ≤ FiniteSum.listSum rest value := by
      clear ih
      induction rest with
      | nil => change (0 : Rat) ≤ 0; decide
      | cons item tail ih => exact Rat.add_nonneg (nonnegative item) ih
    have headNonnegative := nonnegative first
    rw [FiniteSum.listSum]
    constructor
    · intro zero item member
      have headZero : value first = 0 := by grind only
      have tailZero : FiniteSum.listSum rest value = 0 := by grind only
      rcases List.mem_cons.mp member with rfl | member
      · exact headZero
      · exact ih.mp tailZero item member
    · intro zero
      rw [zero first (by simp), ih.mpr (fun item member => zero item (by simp [member]))]
      exact Rat.add_zero 0

/-- Nonnegative exact finite sums vanish precisely on the empty nonzero support. -/
theorem hasSum_zero_iff {value : α → Rat} {result : Rat} (sum : FiniteSum.HasSum value result)
    (nonnegative : ∀ item, 0 ≤ value item) : result = 0 ↔ ∀ item, value item = 0 := by
  obtain ⟨items, _, cover, total⟩ := sum
  rw [← total, listSum_zero_iff items value nonnegative]
  constructor
  · intro zeros item
    by_cases zero : value item = 0
    · exact zero
    · exact zeros item (cover item zero)
  · exact fun zeros item _ => zeros item

/-- Natural-valued semantics is nonnegative at every assignment. -/
theorem natural_nonnegative (value : α → Rat) (natural : ∀ item, ∃ n : Nat, value item = (n : Rat)) :
    ∀ item, 0 ≤ value item := by
  intro item
  obtain ⟨n, valueEq⟩ := natural item
  rw [valueEq]
  exact Rat.natCast_nonneg

/-- Updating a variable with its original value preserves the complete assignment. -/
theorem update_self (assignment : Nat → Int) (index : Nat) :
    LatticeBound.update assignment index (assignment index) = assignment := by
  funext other
  by_cases same : other = index <;> simp [LatticeBound.update, same]

/-- Iterated exact summation preserves whether the whole nonnegative function is zero. -/
theorem sumsOut_zero_iff (order : List Nat) (initial result : (Nat → Int) → Rat)
    (summed : SumsOut order initial result)
    (natural : ∀ assignment, ∃ n : Nat, initial assignment = (n : Rat)) :
    (∀ assignment, result assignment = 0) ↔ ∀ assignment, initial assignment = 0 := by
  induction order generalizing initial with
  | nil => simp only [SumsOut] at summed; simp [summed]
  | cons index rest ih =>
    obtain ⟨next, step, later⟩ := summed
    have nextNatural : ∀ assignment, ∃ n : Nat, next assignment = (n : Rat) := by
      intro assignment
      exact FiniteSum.natural (step assignment) (fun value => natural (LatticeBound.update assignment index value))
    rw [ih next later nextNatural]
    constructor
    · intro zero assignment
      have each := (hasSum_zero_iff (step assignment)
        (fun value => natural_nonnegative initial natural (LatticeBound.update assignment index value))).mp (zero assignment)
      have original := each (assignment index)
      rwa [update_self] at original
    · intro zero assignment
      exact (hasSum_zero_iff (step assignment)
        (fun value => natural_nonnegative initial natural (LatticeBound.update assignment index value))).mpr
        (fun value => zero (LatticeBound.update assignment index value))

/-- The compiled indicator is zero precisely when its interpreted formula is not true. -/
theorem initial_zero_iff [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (parsed : signed (variableOf names) true formula = .ok compiled)
    (assignment : Nat → Int) :
    total (LatticeInput.initial compiled) assignment = 0 ↔
      evaluateFormula (nameValues names assignment) formula ≠ some true := by
  obtain ⟨value, interpreted, counted⟩ := initial_indicator names formula compiled parsed assignment
  rw [counted, interpreted]
  cases value <;> decide

/-- The actual final count is zero exactly when no integer assignment satisfies the formula. -/
theorem count_zero_iff [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (parsed : signed (variableOf names) true formula = .ok compiled)
    (output : List LatticePiece.Piece)
    (success : sumOut (List.range names.length).reverse (LatticeInput.initial compiled) (initial_valid compiled) = .ok output) :
    polynomialCount output = 0 ↔
      ∀ assignment, evaluateFormula (nameValues names assignment) formula ≠ some true := by
  have natural : ∀ assignment, ∃ n : Nat, total (LatticeInput.initial compiled) assignment = (n : Rat) := by
    intro assignment
    obtain ⟨value, _, counted⟩ := initial_indicator names formula compiled parsed assignment
    cases value
    · exact ⟨0, counted⟩
    · exact ⟨1, counted⟩
  have zeros := sumsOut_zero_iff _ _ _ (count_correct names formula compiled parsed output success) natural
  have constantZero : (∀ _ : Nat → Int, polynomialCount output = 0) ↔ polynomialCount output = 0 := by
    constructor
    · exact fun allZero => allZero (fun _ => 0)
    · exact fun zero _ => zero
  rw [constantZero] at zeros
  rw [zeros]
  exact forall_congr' (fun assignment => initial_zero_iff names formula compiled parsed assignment)

/-- A successful count's integral conversion cannot take the source error branch. -/
theorem count_integral [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (parsed : signed (variableOf names) true formula = .ok compiled)
    (output : List LatticePiece.Piece)
    (success : sumOut (List.range names.length).reverse (LatticeInput.initial compiled) (initial_valid compiled) = .ok output) :
    (polynomialCount output).den = 1 ∧ 0 ≤ (polynomialCount output).num := by
  obtain ⟨count, exactCount⟩ := count_natural names formula compiled parsed output success
  rw [exactCount]
  exact ⟨rfl, Int.natCast_nonneg count⟩

end MicroCFTA.LatticeDecision
