import MicroCFTA.LatticeFeasible

/-!
# Concrete signed-conjunction simplification

Signed entries use integer linear inequalities. The executable simplifier
normalizes each conjunction, rejects infeasible conjunctions, adds coefficients
for equal keys, and removes zero coefficients. Proof certificates are erased
from execution. They establish the sparse-map invariant at each recursive call.
-/

namespace MicroCFTA.LatticeSigned
open LatticeLinear Lean.Grind

deriving instance DecidableEq for LatticePolynomial.Linear

/-- A signed map entry contains a conjunction and its integer coefficient. -/
abbrev Signed := List (List Linear × Int)

/-- Every inequality in every entry has a valid sparse coefficient map. -/
def ValidSigned (terms : Signed) : Prop := ∀ entry ∈ terms, ∀ form ∈ entry.1, Valid form

/-- The executable Boolean conjunction at one integer assignment. -/
def region (assignment : Nat → Int) (forms : List Linear) : Bool :=
  forms.all fun form => decide (0 ≤ evaluate assignment form)

/-- Evaluate the signed map at an integer assignment. -/
def score (assignment : Nat → Int) : Signed → Int
  | [] => 0
  | (forms, weight) :: rest => weight * Lattice.indicator (region assignment forms) + score assignment rest

/-- Boolean conjunction has the same meaning as the normalization specification. -/
theorem region_true (assignment : Nat → Int) (forms : List Linear) :
    region assignment forms = true ↔ LatticeNormalize.Satisfies forms assignment := by
  simp [region, LatticeNormalize.Satisfies, List.all_eq_true]

/-- Signed evaluation adds over concatenation. -/
theorem score_append (assignment : Nat → Int) (left right : Signed) :
    score assignment (left ++ right) = score assignment left + score assignment right := by
  induction left with
  | nil => simp [score]
  | cons entry rest ih => simp [score, ih, Int.add_assoc]

/-- Normalization preserves the exact Boolean region. -/
theorem normalize_region (assignment : Nat → Int) (forms result : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (success : LatticeNormalize.normalize forms = some result) :
    region assignment forms = region assignment result := by
  apply Bool.eq_iff_iff.mpr
  rw [region_true, region_true, LatticeNormalize.normalize_correct forms valid assignment]
  constructor
  · rintro ⟨other, found, satisfies⟩
    rw [success] at found
    cases found
    exact satisfies
  · exact fun satisfies => ⟨result, success, satisfies⟩

/-- Normalize every conjunction and apply the source's feasibility filter. -/
def prepare : (terms : Signed) → ValidSigned terms → Signed
  | [], _ => []
  | (forms, weight) :: rest, valid =>
      let tail := prepare rest (fun entry member => valid entry (by simp [member]))
      match found : LatticeNormalize.normalize forms with
      | none => tail
      | some normalized =>
        if LatticeFeasible.feasible normalized
            (LatticeNormalize.normalize_valid forms (valid (forms, weight) (by simp)) normalized found)
        then (normalized, weight) :: tail else tail

/-- Preparation preserves every signed contribution, including negative coefficients. -/
theorem prepare_score (assignment : Nat → Int) (terms : Signed) (valid : ValidSigned terms) :
    score assignment (prepare terms valid) = score assignment terms := by
  induction terms with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨forms, weight⟩
    have head := valid (forms, weight) (by simp)
    have tail : ValidSigned rest := fun entry member => valid entry (by simp [member])
    unfold prepare
    split
    · next missing =>
      have empty : region assignment forms = false := by
        cases isTrue : region assignment forms
        · rfl
        · exact False.elim (LatticeNormalize.normalize_none forms head missing assignment
            ((region_true assignment forms).mp isTrue))
      simp [score, empty, Lattice.indicator, ih tail]
    · next normalized found =>
      have normalizedValid := LatticeNormalize.normalize_valid forms head normalized found
      split
      · next feasible =>
        simp only [score, ih tail, normalize_region assignment forms normalized head found]
      · next infeasible =>
        have empty : region assignment forms = false := by
          cases isTrue : region assignment forms
          · rfl
          · have kept : LatticeNormalize.Satisfies normalized assignment := by
              apply (region_true assignment normalized).mp
              rwa [← normalize_region assignment forms normalized head found]
            exact False.elim (infeasible (LatticeFeasible.feasible_of_satisfies normalized normalizedValid assignment kept))
        simp [score, empty, Lattice.indicator, ih tail]

/-- Preparation retains the coefficient-map invariant for every surviving entry. -/
theorem prepare_valid (terms : Signed) (valid : ValidSigned terms) : ValidSigned (prepare terms valid) := by
  induction terms with
  | nil => simp [prepare, ValidSigned]
  | cons entry rest ih =>
    rcases entry with ⟨forms, weight⟩
    have head := valid (forms, weight) (by simp)
    have tail : ValidSigned rest := fun entry member => valid entry (by simp [member])
    unfold prepare
    split
    · exact ih tail
    · next normalized found =>
      split
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact LatticeNormalize.normalize_valid forms head normalized found
        · exact ih tail entry member
      · exact ih tail

/-- Insert a map entry, adding its coefficient to an equal conjunction key. -/
def insert (forms : List Linear) (weight : Int) : Signed → Signed
  | [] => [(forms, weight)]
  | (other, old) :: rest =>
      if forms = other then (other, weight + old) :: rest
      else (other, old) :: insert forms weight rest

/-- Map insertion preserves the sum of signed contributions. -/
theorem insert_score (assignment : Nat → Int) (forms : List Linear) (weight : Int) (terms : Signed) :
    score assignment (insert forms weight terms) =
      weight * Lattice.indicator (region assignment forms) + score assignment terms := by
  induction terms with
  | nil => simp [insert, score]
  | cons entry rest ih =>
    rcases entry with ⟨other, old⟩
    by_cases same : forms = other
    · simp [insert, same, score, Int.add_mul, Int.add_assoc]
    · simp [insert, same, score, ih]
      grind

/-- Insertion preserves the invariant when its key and all existing keys are valid. -/
theorem insert_valid (forms : List Linear) (weight : Int) (terms : Signed)
    (head : ∀ form ∈ forms, Valid form) (tail : ValidSigned terms) : ValidSigned (insert forms weight terms) := by
  induction terms with
  | nil => simpa [insert, ValidSigned] using head
  | cons entry rest ih =>
    rcases entry with ⟨other, old⟩
    by_cases same : forms = other
    · simp only [insert, same, ↓reduceIte]
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact tail (other, old) (by simp)
      · exact tail entry (by simp [member])
    · simp only [insert, same, ↓reduceIte]
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact tail (other, old) (by simp)
      · exact ih (fun entry member => tail entry (by simp [member])) entry member

/-- Build the source's map with addition on duplicate conjunction keys. -/
def merge : Signed → Signed
  | [] => []
  | (forms, weight) :: rest => insert forms weight (merge rest)

/-- Coefficient merging preserves the signed indicator. -/
theorem merge_score (assignment : Nat → Int) (terms : Signed) : score assignment (merge terms) = score assignment terms := by
  induction terms with
  | nil => rfl
  | cons entry rest ih => simp [merge, insert_score, ih, score]

/-- Coefficient merging preserves valid conjunctions. -/
theorem merge_valid (terms : Signed) (valid : ValidSigned terms) : ValidSigned (merge terms) := by
  induction terms with
  | nil => simp [merge, ValidSigned]
  | cons entry rest ih =>
    exact insert_valid entry.1 entry.2 _ (valid entry (by simp))
      (ih (fun entry member => valid entry (by simp [member])))

/-- Drop precisely the entries whose merged coefficient is zero. -/
def removeZeros (terms : Signed) : Signed := terms.filter (fun entry => entry.2 != 0)

/-- A canceled entry contributes zero at every assignment. -/
theorem removeZeros_score (assignment : Nat → Int) (terms : Signed) :
    score assignment (removeZeros terms) = score assignment terms := by
  induction terms with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨forms, weight⟩
    by_cases zero : weight = 0 <;> simp [removeZeros, zero, score, ← ih]

/-- Removing entries preserves the conjunction invariant. -/
theorem removeZeros_valid (terms : Signed) (valid : ValidSigned terms) : ValidSigned (removeZeros terms) := by
  intro entry member
  exact valid entry (List.mem_filter.mp member).1

/-- The full executable signed-map simplifier. -/
def simplify (terms : Signed) (valid : ValidSigned terms) : Signed := removeZeros (merge (prepare terms valid))

/-- Every stage of simplification preserves the exact signed indicator. -/
theorem simplify_score (assignment : Nat → Int) (terms : Signed) (valid : ValidSigned terms) :
    score assignment (simplify terms valid) = score assignment terms := by
  rw [simplify, removeZeros_score, merge_score, prepare_score]

/-- The simplifier produces valid inputs for every later operation. -/
theorem simplify_valid (terms : Signed) (valid : ValidSigned terms) : ValidSigned (simplify terms valid) :=
  removeZeros_valid _ (merge_valid _ (prepare_valid terms valid))

/-- Preparation retains any property established for every successful normalized key. -/
theorem prepare_property (property : List Linear → Prop) (terms : Signed) (valid : ValidSigned terms)
    (preserved : ∀ entry ∈ terms, ∀ forms, LatticeNormalize.normalize entry.1 = some forms → property forms) :
    ∀ entry ∈ prepare terms valid, property entry.1 := by
  induction terms with
  | nil => simp [prepare]
  | cons entry rest ih =>
    rcases entry with ⟨forms, weight⟩
    have tail := ih (fun entry member => valid entry (by simp [member]))
      (fun entry member => preserved entry (by simp [member]))
    unfold prepare
    split
    · exact tail
    · next normalized found =>
      split
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact preserved (forms, weight) (by simp) normalized found
        · exact tail entry member
      · exact tail

/-- Adding a coefficient preserves any property of the conjunction keys. -/
theorem insert_property (property : List Linear → Prop) (forms : List Linear) (weight : Int) (terms : Signed)
    (head : property forms) (tail : ∀ entry ∈ terms, property entry.1) :
    ∀ entry ∈ insert forms weight terms, property entry.1 := by
  induction terms with
  | nil => simpa [insert] using head
  | cons entry rest ih =>
    rcases entry with ⟨other, old⟩
    by_cases same : forms = other
    · simp only [insert, same, ↓reduceIte]
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact tail (other, old) (by simp)
      · exact tail entry (by simp [member])
    · simp only [insert, same, ↓reduceIte]
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact tail (other, old) (by simp)
      · exact ih (fun entry member => tail entry (by simp [member])) entry member

/-- Merging duplicate keys preserves every property of the original keys. -/
theorem merge_property (property : List Linear → Prop) (terms : Signed)
    (preserved : ∀ entry ∈ terms, property entry.1) : ∀ entry ∈ merge terms, property entry.1 := by
  induction terms with
  | nil => simp [merge]
  | cons entry rest ih =>
    exact insert_property property entry.1 entry.2 _ (preserved entry (by simp))
      (ih (fun entry member => preserved entry (by simp [member])))

/-- Full simplification preserves properties of its normalized conjunction keys. -/
theorem simplify_property (property : List Linear → Prop) (terms : Signed) (valid : ValidSigned terms)
    (preserved : ∀ entry ∈ terms, ∀ forms, LatticeNormalize.normalize entry.1 = some forms → property forms) :
    ∀ entry ∈ simplify terms valid, property entry.1 := by
  intro entry member
  exact merge_property property _ (prepare_property property terms valid preserved) entry
    (List.mem_filter.mp member).1

/-- Every simplified conjunction has had all constant inequalities removed. -/
theorem simplify_nonconstant (terms : Signed) (valid : ValidSigned terms) :
    ∀ entry ∈ simplify terms valid, ∀ form ∈ entry.1, form.coefficients ≠ [] :=
  simplify_property _ terms valid (fun entry _ forms success =>
    LatticeNormalize.normalize_nonconstant entry.1 forms success)

/-- A signed map carries the invariant derived by its constructors. -/
structure Checked where
  terms : Signed
  valid : ValidSigned terms
  nonconstant : ∀ entry ∈ terms, ∀ form ∈ entry.1, form.coefficients ≠ []

/-- Simplify and retain the proved invariant for subsequent constructors. -/
def checked (terms : Signed) (valid : ValidSigned terms) : Checked :=
  ⟨simplify terms valid, simplify_valid terms valid, simplify_nonconstant terms valid⟩

/-- The source's universally true signed formula. -/
def always : Checked := ⟨[([], 1)], by simp [ValidSigned], by simp⟩

/-- The source's universally false signed formula. -/
def never : Checked := ⟨[], by simp [ValidSigned], by simp⟩

/-- Build one signed conjunction with coefficient one. -/
def single (forms : List Linear) (valid : ∀ form ∈ forms, Valid form) : Checked :=
  checked [(forms, 1)] (by simpa [ValidSigned] using valid)

/-- Conjunction multiplies every pair of entries. -/
def product (left right : Signed) : Signed :=
  left.flatMap fun (leftForms, leftSign) =>
    right.map fun (rightForms, rightSign) => (leftForms ++ rightForms, leftSign * rightSign)

/-- Appended conjunctions denote Boolean conjunction. -/
theorem region_append (assignment : Nat → Int) (left right : List Linear) :
    region assignment (left ++ right) = (region assignment left && region assignment right) := by
  simp [region]

/-- Multiplying entries produces the product of their signed scores. -/
theorem product_score (assignment : Nat → Int) (left right : Signed) :
    score assignment (product left right) = score assignment left * score assignment right := by
  induction left with
  | nil => simp [product, score]
  | cons entry rest ih =>
    rcases entry with ⟨forms, sign⟩
    simp only [product, List.flatMap_cons, score_append, score] at *
    rw [ih]
    have row : score assignment (right.map fun (other, weight) => (forms ++ other, sign * weight)) =
        sign * Lattice.indicator (region assignment forms) * score assignment right := by
      clear ih
      induction right with
      | nil => simp [score]
      | cons entry rest ih =>
        rcases entry with ⟨other, weight⟩
        simp only [List.map_cons, score, region_append, Lattice.indicator_and, ih]
        grind
    rw [row]
    grind

/-- Product construction preserves each constituent coefficient map. -/
theorem product_valid (left right : Signed) (hl : ValidSigned left) (hr : ValidSigned right) :
    ValidSigned (product left right) := by
  intro entry member form present
  obtain ⟨leftEntry, leftMember, row⟩ := List.mem_flatMap.mp member
  obtain ⟨rightEntry, rightMember, rfl⟩ := List.mem_map.mp row
  rcases List.mem_append.mp present with leftPresent | rightPresent
  · exact hl leftEntry leftMember form leftPresent
  · exact hr rightEntry rightMember form rightPresent

/-- Execute conjunction and the full source simplifier. -/
def conjoin (left right : Checked) : Checked :=
  checked (product left.terms right.terms) (product_valid _ _ left.valid right.valid)

/-- Executable conjunction multiplies its inputs' signed scores. -/
theorem conjoin_score (assignment : Nat → Int) (left right : Checked) :
    score assignment (conjoin left right).terms = score assignment left.terms * score assignment right.terms := by
  simp only [conjoin, checked, simplify_score, product_score]

/-- Negate every coefficient as required by inclusion and exclusion. -/
def negate (terms : Signed) : Signed := terms.map fun (forms, weight) => (forms, -weight)

/-- Negating coefficients negates the signed score. -/
theorem negate_score (assignment : Nat → Int) (terms : Signed) :
    score assignment (negate terms) = -score assignment terms := by
  induction terms with
  | nil => simp [negate, score]
  | cons entry rest ih =>
    simp only [negate, List.map_cons, score] at *
    rw [ih]
    grind

/-- Negation changes no conjunction key. -/
theorem negate_valid (terms : Signed) (valid : ValidSigned terms) : ValidSigned (negate terms) := by
  intro entry member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact valid original present

/-- Append two checked entry lists. -/
theorem append_valid (left right : Signed) (hl : ValidSigned left) (hr : ValidSigned right) :
    ValidSigned (left ++ right) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact hl entry member
  · exact hr entry member

/-- Execute disjunction with a simplified conjunction for its overlap term. -/
def disjoin (left right : Checked) : Checked :=
  checked (left.terms ++ right.terms ++ negate (conjoin left right).terms)
    (append_valid _ _ (append_valid _ _ left.valid right.valid)
      (negate_valid _ (conjoin left right).valid))

/-- Executable disjunction implements inclusion and exclusion exactly. -/
theorem disjoin_score (assignment : Nat → Int) (left right : Checked) :
    score assignment (disjoin left right).terms =
      score assignment left.terms + score assignment right.terms -
        score assignment left.terms * score assignment right.terms := by
  simp only [disjoin, checked, simplify_score, score_append, negate_score, conjoin_score]
  grind

/-- A single conjunction contributes its exact zero-or-one indicator. -/
theorem single_score (assignment : Nat → Int) (forms : List Linear) (valid : ∀ form ∈ forms, Valid form) :
    score assignment (single forms valid).terms = Lattice.indicator (region assignment forms) := by
  simp [single, checked, simplify_score, score]

/-- Integer relations supported by the source atom compiler. -/
inductive Relation where
  | le | lt | ge | gt | eq | ne | ueq | une
  deriving DecidableEq

/-- Interpret each relation directly over integers. -/
def relationHolds : Relation → Int → Int → Bool
  | .le, left, right => decide (left ≤ right)
  | .lt, left, right => decide (left < right)
  | .ge, left, right => decide (right ≤ left)
  | .gt, left, right => decide (right < left)
  | .eq, left, right | .ueq, left, right => decide (left = right)
  | .ne, left, right | .une, left, right => decide (left ≠ right)

/-- Complement an integer relation at a negated atom. -/
def opposite : Relation → Relation
  | .le => .gt | .lt => .ge | .ge => .lt | .gt => .le
  | .eq => .ne | .ne => .eq | .ueq => .une | .une => .ueq

/-- Relation complementation is exact over integers. -/
theorem opposite_correct (relation : Relation) (left right : Int) :
    relationHolds (opposite relation) left right = !relationHolds relation left right := by
  cases relation <;> apply Bool.eq_iff_iff.mpr <;> simp [opposite, relationHolds] <;> omega

/-- The difference of right minus left has the source's eight relation encodings. -/
def atom (relation : Relation) (difference : Linear) (valid : Valid difference) : Checked :=
  let positive := single [difference] (by simpa using valid)
  let negative := single [scale (-1) difference] (by simpa using scale_valid (-1) difference valid)
  let strictPositive := single [minus difference (constant 1)]
    (by simpa using minus_valid difference (constant 1) valid (constant_valid 1))
  let strictNegative := single [minus (scale (-1) difference) (constant 1)]
    (by simpa using minus_valid _ (constant 1) (scale_valid (-1) difference valid) (constant_valid 1))
  let equal := single [difference, scale (-1) difference]
    (by intro form member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact valid
        · exact scale_valid (-1) difference valid)
  match relation with
  | .le => positive
  | .lt => strictPositive
  | .ge => negative
  | .gt => strictNegative
  | .eq | .ueq => equal
  | .ne | .une => disjoin strictPositive strictNegative

/-- Atomic compilation preserves the exact integer relation, including disequality. -/
theorem atom_score (assignment : Nat → Int) (relation : Relation) (difference : Linear)
    (valid : Valid difference) (left right : Int) (value : evaluate assignment difference = right - left) :
    score assignment (atom relation difference valid).terms =
      Lattice.indicator (relationHolds relation left right) := by
  have nonnegative : (0 ≤ right - left) ↔ left ≤ right := by omega
  have positive : (0 ≤ right - left - 1) ↔ left < right := by omega
  have nonpositive : (0 ≤ -1 * (right - left)) ↔ right ≤ left := by omega
  have negative : (0 ≤ -1 * (right - left) - 1) ↔ right < left := by omega
  cases relation <;>
    simp only [atom, single_score, disjoin_score, region, List.all_cons, List.all_nil,
      Bool.and_true, evaluate_minus, evaluate_scale, evaluate_constant, value, relationHolds,
      nonnegative, positive, nonpositive, negative]
  all_goals
    rcases Int.lt_trichotomy left right with less | equal | greater
    · have le : left ≤ right := by omega
      have nle : ¬right ≤ left := by omega
      have nlt : ¬right < left := by omega
      have ne : left ≠ right := by omega
      simp [Lattice.indicator, less, le, nle, nlt, ne]
    · subst right; simp [Lattice.indicator]
    · have le : right ≤ left := by omega
      have nle : ¬left ≤ right := by omega
      have nlt : ¬left < right := by omega
      have ne : left ≠ right := by omega
      simp [Lattice.indicator, greater, le, nle, nlt, ne]

end MicroCFTA.LatticeSigned
