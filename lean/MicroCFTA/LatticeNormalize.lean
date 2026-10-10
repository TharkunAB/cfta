import MicroCFTA.LatticeLinear
import MicroCFTA.Lattice

/-!
# Normalization of integer linear inequalities

The executable stages follow `Refinement.Lattice.normalize`: remove constant
inequalities, divide by the coefficient gcd, retain the least offset of each
direction, and detect contradictory opposite directions.
-/

namespace MicroCFTA.LatticeNormalize
open LatticeLinear Lean.Grind

/-- A conjunction requires every integer linear form to be nonnegative. -/
def Satisfies (forms : List Linear) (assignment : Nat → Int) : Prop :=
  ∀ form ∈ forms, 0 ≤ evaluate assignment form

/-- The gcd of the absolute values of all coefficients. -/
def divisor : List (Nat × Int) → Nat
  | [] => 0
  | (_, coefficient) :: rest => Nat.gcd coefficient.natAbs (divisor rest)

/-- The computed gcd divides every coefficient. -/
theorem divisor_dvd (coefficients : List (Nat × Int)) (entry : Nat × Int) (member : entry ∈ coefficients) :
    (divisor coefficients : Int) ∣ entry.2 := by
  apply Int.ofNat_dvd_left.mpr
  induction coefficients with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · subst entry
      exact Nat.gcd_dvd_left ..
    · exact Nat.dvd_trans (Nat.gcd_dvd_right ..) (ih tail)

/-- A nonempty coefficient map with no zero values has positive gcd. -/
theorem divisor_positive (coefficients : List (Nat × Int)) (nonempty : coefficients ≠ [])
    (nonzero : ∀ entry ∈ coefficients, entry.2 ≠ 0) : 0 < divisor coefficients := by
  cases coefficients with
  | nil => contradiction
  | cons first rest =>
    have hn : first.2.natAbs ≠ 0 := by
      intro zero
      exact nonzero first (by simp) (Int.natAbs_eq_zero.mp zero)
    exact Nat.gcd_pos_of_pos_left _ (by omega)

/-- Exact coefficient division uses truncating division, as Haskell `quot` does. -/
def divideCoefficients (d : Int) (coefficients : List (Nat × Int)) : List (Nat × Int) :=
  coefficients.map (fun (index, coefficient) => (index, coefficient.tdiv d))

/-- Multiplying the divided variable part by the divisor recovers its original value. -/
theorem divided_value (assignment : Nat → Int) (d : Int) (coefficients : List (Nat × Int))
    (divides : ∀ entry ∈ coefficients, d ∣ entry.2) :
    d * evalCoefficients assignment (divideCoefficients d coefficients) = evalCoefficients assignment coefficients := by
  induction coefficients with
  | nil => simp [divideCoefficients, evalCoefficients]
  | cons entry rest ih =>
    rcases entry with ⟨index, coefficient⟩
    have head := Int.mul_tdiv_cancel' (divides (index, coefficient) (by simp))
    have tail := ih (fun entry member => divides entry (List.mem_cons_of_mem _ member))
    simp only [divideCoefficients, List.map_cons, evalCoefficients] at *
    grind

/-- Divide coefficients exactly and round the offset down. -/
def reduceByGcd (linear : Linear) : Linear :=
  let d : Int := divisor linear.coefficients
  ⟨divideCoefficients d linear.coefficients, linear.offset / d⟩

/-- Gcd reduction preserves the inequality at every integer assignment. -/
theorem reduceByGcd_correct (linear : Linear) (valid : Valid linear)
    (nonempty : linear.coefficients ≠ []) (assignment : Nat → Int) :
    0 ≤ evaluate assignment linear ↔ 0 ≤ evaluate assignment (reduceByGcd linear) := by
  have positive : 0 < (divisor linear.coefficients : Int) := by
    exact_mod_cast divisor_positive linear.coefficients nonempty valid.2
  have restored := divided_value assignment (divisor linear.coefficients) linear.coefficients
    (divisor_dvd linear.coefficients)
  simp only [evaluate, reduceByGcd]
  have result := Lattice.normalize_divisor (divisor linear.coefficients)
    (evalCoefficients assignment (divideCoefficients (divisor linear.coefficients) linear.coefficients))
    linear.offset positive
  rw [restored] at result
  simpa [Int.add_comm] using result

/-- Gcd reduction keeps the sparse map invariant. -/
theorem reduceByGcd_valid (linear : Linear) (valid : Valid linear) : Valid (reduceByGcd linear) := by
  constructor
  · simpa [reduceByGcd, divideCoefficients, Sparse.Ordered, List.pairwise_map] using valid.1
  · intro entry member
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    subst entry
    intro zero
    have restored := Int.mul_tdiv_cancel' (divisor_dvd linear.coefficients original present)
    have quotient : original.2.tdiv (divisor linear.coefficients) = 0 := zero
    rw [quotient, Int.mul_zero] at restored
    exact valid.2 original present restored.symm

/-- A constant either disappears or refutes the conjunction. Other forms are gcd-reduced. -/
def reduce (linear : Linear) : Option (List Linear) :=
  if linear.coefficients.isEmpty then
    if 0 ≤ linear.offset then some [] else none
  else some [reduceByGcd linear]

/-- Reducing one form preserves exactly its integer solutions. -/
theorem reduce_correct (linear : Linear) (valid : Valid linear) (assignment : Nat → Int) :
    0 ≤ evaluate assignment linear ↔
      ∃ forms, reduce linear = some forms ∧ Satisfies forms assignment := by
  by_cases empty : linear.coefficients = []
  · by_cases nonnegative : 0 ≤ linear.offset <;>
      simp [reduce, empty, nonnegative, evaluate, evalCoefficients, Satisfies]
  · simpa [reduce, empty, Satisfies] using reduceByGcd_correct linear valid empty assignment

/-- Reduce each form, failing as soon as a constant contradiction is found. -/
def reduceAll : List Linear → Option (List Linear)
  | [] => some []
  | form :: rest => do
      let first ← reduce form
      let remaining ← reduceAll rest
      some (first ++ remaining)

/-- A conjunction's list semantics distributes over concatenation. -/
theorem satisfies_append (left right : List Linear) (assignment : Nat → Int) :
    Satisfies (left ++ right) assignment ↔ Satisfies left assignment ∧ Satisfies right assignment := by
  simp only [Satisfies, List.mem_append, or_imp, _root_.forall_and]

/-- Reducing the entire list preserves exactly the original integer solutions. -/
theorem reduceAll_correct (forms : List Linear) (valid : ∀ form ∈ forms, Valid form) (assignment : Nat → Int) :
    Satisfies forms assignment ↔
      ∃ reduced, reduceAll forms = some reduced ∧ Satisfies reduced assignment := by
  induction forms with
  | nil => simp [reduceAll, Satisfies]
  | cons form rest ih =>
    have head := reduce_correct form (valid form (by simp)) assignment
    have tail := ih (fun other member => valid other (by simp [member]))
    have split : Satisfies (form :: rest) assignment ↔
        0 ≤ evaluate assignment form ∧ Satisfies rest assignment := by simp [Satisfies]
    rw [split, head, tail]
    cases first : reduce form <;> cases remaining : reduceAll rest <;>
      simp [reduceAll, first, remaining, satisfies_append]

@[simp] theorem satisfies_cons (form : Linear) (rest : List Linear) (assignment : Nat → Int) :
    Satisfies (form :: rest) assignment ↔ 0 ≤ evaluate assignment form ∧ Satisfies rest assignment := by
  simp [Satisfies]

/-- Every successful individual reduction retains valid sparse maps. -/
theorem reduce_valid (linear : Linear) (valid : Valid linear) (forms : List Linear)
    (success : reduce linear = some forms) : ∀ form ∈ forms, Valid form := by
  unfold reduce at success
  split at success
  · split at success
    · cases success; simp
    · cases success
  · cases success
    intro form member
    have same : form = reduceByGcd linear := by simpa using member
    subst form
    exact reduceByGcd_valid linear valid

/-- List reduction retains valid sparse maps throughout the conjunction. -/
theorem reduceAll_valid (forms : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (reduced : List Linear) (success : reduceAll forms = some reduced) :
    ∀ form ∈ reduced, Valid form := by
  induction forms generalizing reduced with
  | nil => simp [reduceAll] at success; subst reduced; simp
  | cons first rest ih =>
    cases head : reduce first <;> cases tail : reduceAll rest <;>
      simp [reduceAll, head, tail] at success
    subst reduced
    intro form member
    rcases List.mem_append.mp member with left | right
    · exact reduce_valid first (valid first (by simp)) _ head form left
    · exact ih (fun other member => valid other (by simp [member])) _ tail form right

/-- Insert one direction, keeping its least constant offset. -/
def insertTightest (form : Linear) : List Linear → List Linear
  | [] => [form]
  | old :: rest =>
      if form.coefficients = old.coefficients then
        ⟨old.coefficients, min form.offset old.offset⟩ :: rest
      else old :: insertTightest form rest

/-- Tightest-offset insertion is exactly conjunction with the new inequality. -/
theorem insertTightest_correct (form : Linear) (forms : List Linear) (assignment : Nat → Int) :
    Satisfies (insertTightest form forms) assignment ↔
      0 ≤ evaluate assignment form ∧ Satisfies forms assignment := by
  induction forms with
  | nil => simp [insertTightest, Satisfies]
  | cons old rest ih =>
    by_cases same : form.coefficients = old.coefficients
    · simp only [insertTightest, same, ↓reduceIte, satisfies_cons]
      change (0 ≤ min form.offset old.offset + evalCoefficients assignment old.coefficients ∧
          Satisfies rest assignment) ↔
        (0 ≤ form.offset + evalCoefficients assignment form.coefficients ∧
          (0 ≤ old.offset + evalCoefficients assignment old.coefficients ∧ Satisfies rest assignment))
      rw [same]
      by_cases ordered : form.offset ≤ old.offset
      · rw [Int.min_eq_left ordered]
        constructor
        · intro accepted
          exact ⟨accepted.1, by omega, accepted.2⟩
        · intro accepted
          exact ⟨accepted.1, accepted.2.2⟩
      · rw [Int.min_eq_right (by omega)]
        constructor
        · intro accepted
          exact ⟨by omega, accepted.1, accepted.2⟩
        · intro accepted
          exact accepted.2
    · simp only [insertTightest, same, ↓reduceIte, satisfies_cons, ih]
      grind only

/-- Normalize the direction map with a minimum-offset insertion fold. -/
def tighten : List Linear → List Linear
  | [] => []
  | first :: rest => insertTightest first (tighten rest)

/-- Keeping the tightest form in every direction preserves every integer solution. -/
theorem tighten_correct (forms : List Linear) (assignment : Nat → Int) :
    Satisfies (tighten forms) assignment ↔ Satisfies forms assignment := by
  induction forms with
  | nil => rfl
  | cons first rest ih => rw [tighten, insertTightest_correct, ih, satisfies_cons]

/-- Negate a coefficient direction without changing its indices. -/
def opposite (coefficients : List (Nat × Int)) : List (Nat × Int) :=
  coefficients.map (fun (index, coefficient) => (index, -coefficient))

/-- The opposite direction evaluates to the negation of the original variable part. -/
theorem eval_opposite (assignment : Nat → Int) (coefficients : List (Nat × Int)) :
    evalCoefficients assignment (opposite coefficients) = -evalCoefficients assignment coefficients := by
  simpa [opposite] using eval_scaleCoefficients assignment (-1) coefficients

/-- Opposite directions with a negative offset sum cannot both hold. -/
def contradicts (left right : Linear) : Bool :=
  decide (right.coefficients = opposite left.coefficients ∧ left.offset + right.offset < 0)

/-- Search the finite direction map for an opposing inconsistent pair. -/
def hasContradiction (forms : List Linear) : Bool :=
  forms.any (fun left => forms.any (contradicts left))

/-- Every contradiction reported by the executable pair search refutes the conjunction. -/
theorem hasContradiction_sound (forms : List Linear) (reported : hasContradiction forms = true)
    (assignment : Nat → Int) : ¬Satisfies forms assignment := by
  simp only [hasContradiction, List.any_eq_true, contradicts, decide_eq_true_eq] at reported
  obtain ⟨left, leftMember, right, rightMember, directions, offsets⟩ := reported
  intro satisfies
  have hl := satisfies left leftMember
  have hr := satisfies right rightMember
  simp only [evaluate, directions, eval_opposite] at hl hr
  omega

/-- The complete inequality-normalization pipeline. -/
def normalize (forms : List Linear) : Option (List Linear) := do
  let reduced ← reduceAll forms
  let tightest := tighten reduced
  if hasContradiction tightest then none else some tightest

/-- Normalization preserves exactly every integer solution of a valid input conjunction. -/
theorem normalize_correct (forms : List Linear) (valid : ∀ form ∈ forms, Valid form) (assignment : Nat → Int) :
    Satisfies forms assignment ↔
      ∃ normalized, normalize forms = some normalized ∧ Satisfies normalized assignment := by
  rw [reduceAll_correct forms valid assignment]
  cases reduced : reduceAll forms with
  | none => simp [normalize, reduced]
  | some result =>
    simp only [Option.some.injEq]
    by_cases contradiction : hasContradiction (tighten result) = true
    · have impossible : ¬Satisfies result assignment := fun satisfies =>
        hasContradiction_sound _ contradiction assignment ((tighten_correct result assignment).mpr satisfies)
      simp [normalize, reduced, contradiction, impossible]
    · simpa [normalize, reduced, contradiction] using (tighten_correct result assignment).symm

/-- Failure of normalization is a sound proof of integer infeasibility. -/
theorem normalize_none (forms : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (failure : normalize forms = none) : ∀ assignment, ¬Satisfies forms assignment := by
  intro assignment accepted
  obtain ⟨result, success, _⟩ := (normalize_correct forms valid assignment).mp accepted
  rw [failure] at success
  cases success

/-- Tightest-offset insertion preserves all sparse coefficient-map invariants. -/
theorem insertTightest_valid (form : Linear) (forms : List Linear) (head : Valid form)
    (tail : ∀ other ∈ forms, Valid other) :
    ∀ other ∈ insertTightest form forms, Valid other := by
  induction forms with
  | nil => simpa [insertTightest] using head
  | cons first rest ih =>
    by_cases same : form.coefficients = first.coefficients
    · simp only [insertTightest, same, ↓reduceIte, List.mem_cons]
      intro other member
      rcases member with rfl | member
      · exact tail first (by simp)
      · exact tail other (by simp [member])
    · simp only [insertTightest, same, ↓reduceIte, List.mem_cons]
      intro other member
      rcases member with rfl | member
      · exact tail other (by simp)
      · exact ih (fun other member => tail other (by simp [member])) other member

/-- Direction merging preserves valid coefficient maps. -/
theorem tighten_valid (forms : List Linear) (valid : ∀ form ∈ forms, Valid form) :
    ∀ form ∈ tighten forms, Valid form := by
  induction forms with
  | nil => simp [tighten]
  | cons first rest ih =>
    exact insertTightest_valid first _ (valid first (by simp))
      (ih (fun other member => valid other (by simp [member])))

/-- The full successful normalization keeps valid sparse coefficient maps. -/
theorem normalize_valid (forms : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (result : List Linear) (success : normalize forms = some result) :
    ∀ form ∈ result, Valid form := by
  unfold normalize at success
  cases reduced : reduceAll forms with
  | none => simp [reduced] at success
  | some values =>
    cases contradiction : hasContradiction (tighten values) <;> simp [reduced, contradiction] at success
    subst result
    exact tighten_valid values (reduceAll_valid forms valid values reduced)

/-- A linear form mentions only indices in a specified variable universe. -/
def Supported (allowed : Nat → Prop) (form : Linear) : Prop :=
  ∀ entry ∈ form.coefficients, allowed entry.1

/-- Coefficient division does not introduce variable indices. -/
theorem reduceByGcd_supported (allowed : Nat → Prop) (form : Linear)
    (supported : Supported allowed form) : Supported allowed (reduceByGcd form) := by
  intro entry member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact supported original present

/-- Removing constants and reducing gcds does not introduce variable indices. -/
theorem reduce_supported (allowed : Nat → Prop) (form : Linear)
    (supported : Supported allowed form) (result : List Linear)
    (success : reduce form = some result) : ∀ other ∈ result, Supported allowed other := by
  unfold reduce at success
  split at success
  · split at success
    · cases success; simp
    · cases success
  · cases success
    intro other member
    have same : other = reduceByGcd form := by simpa using member
    subst other
    exact reduceByGcd_supported allowed form supported

/-- List reduction stays within its original variable universe. -/
theorem reduceAll_supported (allowed : Nat → Prop) (forms : List Linear)
    (supported : ∀ form ∈ forms, Supported allowed form) (result : List Linear)
    (success : reduceAll forms = some result) : ∀ form ∈ result, Supported allowed form := by
  induction forms generalizing result with
  | nil => simp [reduceAll] at success; subst result; simp
  | cons first rest ih =>
    cases head : reduce first <;> cases tail : reduceAll rest <;>
      simp [reduceAll, head, tail] at success
    subst result
    intro form member
    rcases List.mem_append.mp member with left | right
    · exact reduce_supported allowed first (supported first (by simp)) _ head form left
    · exact ih (fun other member => supported other (by simp [member])) _ tail form right

/-- Insertion changes an offset, not the direction's variable indices. -/
theorem insertTightest_supported (allowed : Nat → Prop) (form : Linear) (forms : List Linear)
    (head : Supported allowed form) (tail : ∀ other ∈ forms, Supported allowed other) :
    ∀ other ∈ insertTightest form forms, Supported allowed other := by
  induction forms with
  | nil => simpa [insertTightest] using head
  | cons first rest ih =>
    by_cases same : form.coefficients = first.coefficients
    · simp only [insertTightest, same, ↓reduceIte, List.mem_cons]
      intro other member
      rcases member with rfl | member
      · exact tail first (by simp)
      · exact tail other (by simp [member])
    · simp only [insertTightest, same, ↓reduceIte, List.mem_cons]
      intro other member
      rcases member with rfl | member
      · exact tail other (by simp)
      · exact ih (fun other member => tail other (by simp [member])) other member

/-- Direction merging stays within the original variable universe. -/
theorem tighten_supported (allowed : Nat → Prop) (forms : List Linear)
    (supported : ∀ form ∈ forms, Supported allowed form) :
    ∀ form ∈ tighten forms, Supported allowed form := by
  induction forms with
  | nil => simp [tighten]
  | cons first rest ih =>
    exact insertTightest_supported allowed first _ (supported first (by simp))
      (ih (fun other member => supported other (by simp [member])))

/-- Successful normalization stays within the original variable universe. -/
theorem normalize_supported (allowed : Nat → Prop) (forms : List Linear)
    (supported : ∀ form ∈ forms, Supported allowed form)
    (result : List Linear) (success : normalize forms = some result) :
    ∀ form ∈ result, Supported allowed form := by
  unfold normalize at success
  cases reduced : reduceAll forms with
  | none => simp [reduced] at success
  | some values =>
    cases contradiction : hasContradiction (tighten values) <;> simp [reduced, contradiction] at success
    subst result
    exact tighten_supported allowed values (reduceAll_supported allowed forms supported values reduced)

end MicroCFTA.LatticeNormalize
