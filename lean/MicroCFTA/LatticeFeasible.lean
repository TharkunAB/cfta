import MicroCFTA.LatticeNormalize
import MicroCFTA.LatticeBound

/-!
# Fourier-Motzkin feasibility filtering

The source combines every positive coefficient with every negative coefficient.
Each combination eliminates one variable. Normalization can then reject the
projected conjunction. Rejection is sound for integer points. Acceptance need
not establish the existence of an integer point.
-/

namespace MicroCFTA.LatticeFeasible
open LatticeLinear LatticeNormalize LatticeBound Lean.Grind

/-- Zero removal preserves the coefficient at each index. -/
theorem coefficient_removeZeros (coefficients : List (Nat × Int)) (index : Nat) :
    Sparse.coefficient (removeZeros coefficients) index = Sparse.coefficient coefficients index := by
  induction coefficients with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, value⟩
    by_cases zero : value = 0 <;> by_cases same : other = index <;>
      simp_all [removeZeros, Sparse.coefficient]

/-- A scalar multiple scales every coefficient. -/
theorem coefficient_scaleMap (coefficients : List (Nat × Int)) (factor : Int) (index : Nat) :
    Sparse.coefficient (coefficients.map fun entry => (entry.1, factor * entry.2)) index =
      factor * Sparse.coefficient coefficients index := by
  induction coefficients with
  | nil => simp [Sparse.coefficient]
  | cons entry rest ih =>
    rcases entry with ⟨other, value⟩
    by_cases same : other = index <;> simp [Sparse.coefficient, same, ih, Int.mul_add]

/-- Exact sparse lookup distributes over addition of canonical forms. -/
theorem coefficientOf_plus (index : Nat) (left right : Linear) (hl : Valid left) (hr : Valid right) :
    coefficientOf index (plus left right) = coefficientOf index left + coefficientOf index right := by
  simp only [coefficientOf, Sparse.valueAtSize_correct _ (plus_valid left right hl hr).1,
    Sparse.valueAtSize_correct _ hl.1, Sparse.valueAtSize_correct _ hr.1]
  exact (coefficient_removeZeros _ index).trans (Sparse.coefficient_addSparse ..)

/-- Exact sparse lookup distributes over scalar multiplication. -/
theorem coefficientOf_scale (index : Nat) (factor : Int) (form : Linear) (valid : Valid form) :
    coefficientOf index (scale factor form) = factor * coefficientOf index form := by
  simp only [coefficientOf, Sparse.valueAtSize_correct _ (scale_valid factor form valid).1,
    Sparse.valueAtSize_correct _ valid.1]
  by_cases zero : factor = 0
  · simp [scale, zero, constant, Sparse.coefficient]
  · simpa [scale, zero] using coefficient_scaleMap form.coefficients factor index

/-- An absent index contributes zero to the coefficient sum. -/
theorem coefficient_absent (coefficients : List (Nat × Int)) (index : Nat)
    (absent : ∀ entry ∈ coefficients, entry.1 ≠ index) : Sparse.coefficient coefficients index = 0 := by
  induction coefficients with
  | nil => rfl
  | cons entry rest ih =>
    simp [Sparse.coefficient, absent entry (by simp), ih (fun entry member => absent entry (by simp [member]))]

/-- In an ordered coefficient map, lookup returns the value at a present index. -/
theorem coefficient_present (coefficients : List (Nat × Int)) (ordered : Sparse.Ordered coefficients)
    (entry : Nat × Int) (member : entry ∈ coefficients) :
    Sparse.coefficient coefficients entry.1 = entry.2 := by
  induction coefficients with
  | nil => simp at member
  | cons first rest ih =>
    have order := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp member with rfl | tail
    · have absent : ∀ other ∈ rest, other.1 ≠ entry.1 := by
        intro other member
        have := order.1 other member
        omega
      simp [Sparse.coefficient, coefficient_absent rest entry.1 absent]
    · have different : first.1 ≠ entry.1 := by have := order.1 entry tail; omega
      simp [Sparse.coefficient, different, ih order.2 tail]

/-- A zero coefficient is absent from a canonical map. -/
theorem coefficientOf_zero_iff (index : Nat) (form : Linear) (valid : Valid form) :
    coefficientOf index form = 0 ↔ ∀ entry ∈ form.coefficients, entry.1 ≠ index := by
  rw [coefficientOf, Sparse.valueAtSize_correct _ valid.1]
  constructor
  · intro zero entry member same
    have value := coefficient_present form.coefficients valid.1 entry member
    rw [same, zero] at value
    exact valid.2 entry member value.symm
  · exact coefficient_absent form.coefficients index

/-- A nonzero coefficient must use an allowed variable. -/
theorem coefficientOf_supported (allowed : Nat → Prop) (index : Nat) (form : Linear)
    (valid : Valid form) (supported : Supported allowed form) (nonzero : coefficientOf index form ≠ 0) :
    allowed index := by
  classical
  by_cases present : allowed index
  · exact present
  · apply False.elim
    apply nonzero
    apply (coefficientOf_zero_iff index form valid).mpr
    intro entry member same
    exact present (same ▸ supported entry member)

/-- Combine one lower inequality and one upper inequality to cancel a variable. -/
def combine (index : Nat) (lower upper : Linear) : Linear :=
  plus (scale (-coefficientOf index upper) lower) (scale (coefficientOf index lower) upper)

/-- Project one variable with the exact source pairing order. -/
def project (index : Nat) (forms : List Linear) : List Linear :=
  forms.filter (fun form => decide (coefficientOf index form = 0)) ++
    (forms.filter (fun form => decide (0 < coefficientOf index form))).flatMap fun lower =>
      (forms.filter (fun form => decide (coefficientOf index form < 0))).map (combine index lower)

/-- Nonnegative combinations preserve every original solution. -/
theorem combine_sound (index : Nat) (lower upper : Linear) (assignment : Nat → Int)
    (positive : 0 < coefficientOf index lower) (negative : coefficientOf index upper < 0)
    (hl : 0 ≤ evaluate assignment lower) (hu : 0 ≤ evaluate assignment upper) :
    0 ≤ evaluate assignment (combine index lower upper) := by
  simp only [combine, evaluate_plus, evaluate_scale]
  have left := Int.mul_nonneg (show 0 ≤ -coefficientOf index upper by omega) hl
  have right := Int.mul_nonneg (show 0 ≤ coefficientOf index lower by omega) hu
  omega

/-- Projection retains every integer solution, without requiring a converse. -/
theorem project_sound (index : Nat) (forms : List Linear) (assignment : Nat → Int)
    (satisfies : Satisfies forms assignment) : Satisfies (project index forms) assignment := by
  intro form member
  rcases List.mem_append.mp member with unchanged | combined
  · exact satisfies form (List.mem_filter.mp unchanged).1
  · obtain ⟨lower, lowerMember, rest⟩ := List.mem_flatMap.mp combined
    obtain ⟨upper, upperMember, rfl⟩ := List.mem_map.mp rest
    exact combine_sound index lower upper assignment
      (of_decide_eq_true (List.mem_filter.mp lowerMember).2)
      (of_decide_eq_true (List.mem_filter.mp upperMember).2)
      (satisfies lower (List.mem_filter.mp lowerMember).1)
      (satisfies upper (List.mem_filter.mp upperMember).1)

/-- Combining canonical forms keeps canonical sparse maps. -/
theorem combine_valid (index : Nat) (lower upper : Linear) (hl : Valid lower) (hu : Valid upper) :
    Valid (combine index lower upper) :=
  plus_valid _ _ (scale_valid _ _ hl) (scale_valid _ _ hu)

/-- Every projected inequality retains its coefficient-map invariant. -/
theorem project_valid (index : Nat) (forms : List Linear) (valid : ∀ form ∈ forms, Valid form) :
    ∀ form ∈ project index forms, Valid form := by
  intro form member
  rcases List.mem_append.mp member with unchanged | combined
  · exact valid form (List.mem_filter.mp unchanged).1
  · obtain ⟨lower, lowerMember, rest⟩ := List.mem_flatMap.mp combined
    obtain ⟨upper, upperMember, rfl⟩ := List.mem_map.mp rest
    exact combine_valid index lower upper (valid lower (List.mem_filter.mp lowerMember).1)
      (valid upper (List.mem_filter.mp upperMember).1)

/-- Every new pair cancels the selected coefficient exactly. -/
theorem combine_cancels (index : Nat) (lower upper : Linear) (hl : Valid lower) (hu : Valid upper) :
    coefficientOf index (combine index lower upper) = 0 := by
  rw [combine, coefficientOf_plus _ _ _ (scale_valid _ _ hl) (scale_valid _ _ hu),
    coefficientOf_scale _ _ _ hl, coefficientOf_scale _ _ _ hu]
  grind

/-- Pair construction introduces no variables outside the original universe. -/
theorem combine_supported (allowed : Nat → Prop) (index : Nat) (lower upper : Linear)
    (hl : Valid lower) (hu : Valid upper) (sl : Supported allowed lower) (su : Supported allowed upper) :
    Supported allowed (combine index lower upper) := by
  intro entry member
  have valid := combine_valid index lower upper hl hu
  have nonzero : coefficientOf entry.1 (combine index lower upper) ≠ 0 := by
    intro zero
    exact (coefficientOf_zero_iff entry.1 _ valid).mp zero entry member rfl
  have expression : coefficientOf entry.1 (combine index lower upper) =
      (-coefficientOf index upper) * coefficientOf entry.1 lower +
        coefficientOf index lower * coefficientOf entry.1 upper := by
    rw [combine, coefficientOf_plus _ _ _ (scale_valid _ _ hl) (scale_valid _ _ hu),
      coefficientOf_scale _ _ _ hl, coefficientOf_scale _ _ _ hu]
  by_cases left : coefficientOf entry.1 lower = 0
  · have right : coefficientOf entry.1 upper ≠ 0 := by
      intro zero
      simp [left, zero] at expression
      exact nonzero expression
    exact coefficientOf_supported allowed entry.1 upper hu su right
  · exact coefficientOf_supported allowed entry.1 lower hl sl left

/-- Projection removes its selected variable and preserves the remaining universe. -/
theorem project_supported (allowed : Nat → Prop) (index : Nat) (forms : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (supported : ∀ form ∈ forms, Supported allowed form) :
    ∀ form ∈ project index forms, Supported (fun other => allowed other ∧ other ≠ index) form := by
  intro form member entry present
  rcases List.mem_append.mp member with unchanged | combined
  · have source := (List.mem_filter.mp unchanged).1
    exact ⟨supported form source entry present,
      (coefficientOf_zero_iff index form (valid form source)).mp
        (of_decide_eq_true (List.mem_filter.mp unchanged).2) entry present⟩
  · obtain ⟨lower, lowerMember, rest⟩ := List.mem_flatMap.mp combined
    obtain ⟨upper, upperMember, rfl⟩ := List.mem_map.mp rest
    have lowerSource := (List.mem_filter.mp lowerMember).1
    have upperSource := (List.mem_filter.mp upperMember).1
    have hl := valid lower lowerSource
    have hu := valid upper upperSource
    exact ⟨combine_supported allowed index lower upper hl hu
      (supported lower lowerSource) (supported upper upperSource) entry present,
      (coefficientOf_zero_iff index _ (combine_valid index lower upper hl hu)).mp
        (combine_cancels index lower upper hl hu) entry present⟩

/-- The finite set of variables, represented without duplicate indices. -/
def variables (forms : List Linear) : List Nat :=
  (forms.flatMap (fun form => form.coefficients.map Prod.fst)).eraseDups

/-- The finite variable universe contains exactly the indices in coefficient maps. -/
theorem mem_variables (index : Nat) (forms : List Linear) :
    index ∈ variables forms ↔ ∃ form ∈ forms, ∃ entry ∈ form.coefficients, entry.1 = index := by
  simp [variables, List.mem_flatMap, List.mem_map]

/-- Erasing repeated indices produces a duplicate-free list. -/
theorem eraseDups_nodup (indices : List Nat) : indices.eraseDups.Nodup := by
  cases indices with
  | nil => simp
  | cons index rest =>
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup (rest.filter (fun other => !other == index))⟩
    simp [List.mem_eraseDups]
termination_by indices.length
decreasing_by have := List.length_filter_le (fun other => !other == index) rest; simp only [List.length_cons]; omega

/-- The computed universe has no duplicate indices. -/
theorem variables_nodup (forms : List Linear) : (variables forms).Nodup := eraseDups_nodup _

/-- Every form is supported by the universe computed from its containing list. -/
theorem variables_support (forms : List Linear) :
    ∀ form ∈ forms, Supported (fun index => index ∈ variables forms) form := by
  intro form member entry present
  exact (mem_variables entry.1 forms).mpr ⟨form, member, entry, present, rfl⟩

/-- A support invariant gives inclusion of the computed variable universe. -/
theorem variables_subset (forms : List Linear) (indices : List Nat)
    (supported : ∀ form ∈ forms, Supported (fun index => index ∈ indices) form) :
    variables forms ⊆ indices := by
  intro index member
  obtain ⟨form, source, entry, present, rfl⟩ := (mem_variables index forms).mp member
  exact supported form source entry present

/-- Normalization cannot increase the number of distinct variables. -/
theorem normalize_variables_le (forms result : List Linear) (success : normalize forms = some result) :
    (variables result).length ≤ (variables forms).length :=
  (variables_nodup result).length_le_of_subset
    (variables_subset result _ (normalize_supported _ forms (variables_support forms) result success))

/-- The source's cost is the number of lower/upper pairs for the variable. -/
def cost (forms : List Linear) (index : Nat) : Nat :=
  (forms.filter (fun form => decide (0 < coefficientOf index form))).length *
    (forms.filter (fun form => decide (coefficientOf index form < 0))).length

/-- Compare the source's `(cost, variable)` candidate pairs. -/
def ScoreLE (forms : List Linear) (left right : Nat) : Prop :=
  cost forms left < cost forms right ∨ cost forms left = cost forms right ∧ left ≤ right

instance (forms : List Linear) (left right : Nat) : Decidable (ScoreLE forms left right) :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- Select the least candidate pair in a finite list. -/
def cheapestFrom (forms : List Linear) : List Nat → Option Nat
  | [] => none
  | first :: rest => match cheapestFrom forms rest with
      | none => some first
      | some best => some (if ScoreLE forms first best then first else best)

/-- Select a variable by the source's minimum-pair heuristic. -/
def cheapest (forms : List Linear) : Option Nat := cheapestFrom forms (variables forms)

/-- The selected minimum is always an input candidate. -/
theorem cheapestFrom_member (forms : List Linear) (candidates : List Nat) (index : Nat)
    (chosen : cheapestFrom forms candidates = some index) : index ∈ candidates := by
  induction candidates with
  | nil => simp [cheapestFrom] at chosen
  | cons first rest ih =>
    cases tail : cheapestFrom forms rest with
    | none => simp [cheapestFrom, tail] at chosen; subst index; simp
    | some best =>
      by_cases compare : ScoreLE forms first best
      · simp [cheapestFrom, tail, compare] at chosen; subst index; simp
      · simp [cheapestFrom, tail, compare] at chosen; subst index
        exact List.mem_cons_of_mem first (ih tail)

/-- Failure to choose a variable means that the candidate list is empty. -/
theorem cheapestFrom_none (forms : List Linear) (candidates : List Nat) :
    cheapestFrom forms candidates = none ↔ candidates = [] := by
  cases candidates with
  | nil => simp [cheapestFrom]
  | cons first rest => cases tail : cheapestFrom forms rest <;> simp [cheapestFrom, tail]

/-- The chosen variable occurs in a coefficient map. -/
theorem cheapest_member (forms : List Linear) (index : Nat) (chosen : cheapest forms = some index) :
    index ∈ variables forms := cheapestFrom_member forms _ index chosen

/-- Minimum candidate selection implements lexicographic cost/index ordering. -/
theorem cheapestFrom_minimal (forms : List Linear) (candidates : List Nat) (index : Nat)
    (chosen : cheapestFrom forms candidates = some index) :
    ∀ other ∈ candidates, ScoreLE forms index other := by
  induction candidates generalizing index with
  | nil => simp [cheapestFrom] at chosen
  | cons first rest ih =>
    cases tail : cheapestFrom forms rest with
    | none =>
      have empty := (cheapestFrom_none forms rest).mp tail
      subst rest
      simp [cheapestFrom] at chosen
      subst index
      simp [ScoreLE]
    | some best =>
      have minimal := ih best tail
      by_cases compare : ScoreLE forms first best
      · simp [cheapestFrom, tail, compare] at chosen
        subst index
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · simp [ScoreLE]
        · have := minimal other member
          unfold ScoreLE at *
          omega
      · simp [cheapestFrom, tail, compare] at chosen
        subst index
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · unfold ScoreLE at *
          omega
        · exact minimal other member

/-- Projection strictly decreases the finite variable universe when it removes a member. -/
theorem project_variables_lt (forms : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (index : Nat) (member : index ∈ variables forms) :
    (variables (project index forms)).length < (variables forms).length := by
  have supported := project_supported (fun other => other ∈ variables forms) index forms valid
    (variables_support forms)
  have subset : variables (project index forms) ⊆ (variables forms).filter (fun other => decide (other ≠ index)) := by
    apply variables_subset
    intro form present entry occurs
    exact List.mem_filter.mpr ⟨(supported form present entry occurs).1,
      decide_eq_true (supported form present entry occurs).2⟩
  have smaller : ((variables forms).filter (fun other => decide (other ≠ index))).length < (variables forms).length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨index, member, by simp⟩
  have bound := (variables_nodup (project index forms)).length_le_of_subset subset
  omega

/-- Each recursive feasibility call strictly decreases the variable universe. -/
theorem step_decreases (forms result : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (normalized : normalize forms = some result) (index : Nat) (chosen : cheapest result = some index) :
    (variables (project index result)).length < (variables forms).length :=
  Nat.lt_of_lt_of_le
    (project_variables_lt result (normalize_valid forms valid result normalized) index
      (cheapest_member result index chosen))
    (normalize_variables_le forms result normalized)

/-- Execute the source's terminating normalization/projection recursion. -/
def feasible (forms : List Linear) (valid : ∀ form ∈ forms, Valid form) : Bool :=
  match normalized : normalize forms with
  | none => false
  | some result => match _chosen : cheapest result with
      | none => true
      | some index => feasible (project index result)
          (project_valid index result (normalize_valid forms valid result normalized))
termination_by (variables forms).length
decreasing_by exact step_decreases forms result valid normalized index _chosen

/-- An existing integer solution survives every recursive feasibility step. -/
theorem feasible_of_satisfies (forms : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (assignment : Nat → Int) (satisfies : Satisfies forms assignment) : feasible forms valid = true := by
  obtain ⟨result, normalized, retained⟩ := (normalize_correct forms valid assignment).mp satisfies
  unfold feasible
  split
  · next missing => rw [missing] at normalized; cases normalized
  · next values found =>
    have same : values = result := Option.some.inj (found.symm.trans normalized)
    subst values
    split
    · rfl
    · next index chosen =>
    exact feasible_of_satisfies (project index result)
      (project_valid index result (normalize_valid forms valid result normalized)) assignment
      (project_sound index result assignment retained)
termination_by (variables forms).length
decreasing_by
  apply step_decreases forms result valid normalized
  assumption

/-- A false feasibility result refutes every integer assignment. -/
theorem feasible_false (forms : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (rejected : feasible forms valid = false) : ∀ assignment, ¬Satisfies forms assignment := by
  intro assignment satisfies
  have accepted := feasible_of_satisfies forms valid assignment satisfies
  rw [rejected] at accepted
  cases accepted

end MicroCFTA.LatticeFeasible
