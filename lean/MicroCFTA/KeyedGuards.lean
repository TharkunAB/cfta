import MicroCFTA.KeyedSource
import MicroCFTA.OccurrenceGuard

/-!
# Source occurrence checks for typed recursive key families

Every placeholder uses the same family token and its own settled minimum.
The source reads size-unguarded, termless, and used flags separately. Its
combined rejection check implies the guard used by the class proofs.
-/
namespace MicroCFTA.KeyedGuards
open KeyedSource

/-- Erase values and masses while retaining the actual per-key probe minimum. -/
def shape (token : Nat) (known : GroupedProbe.Table Key) : Recipe Key Root α → OccurrenceGuard.Shape
  | .finite source | .retained _ _ source => .source (SourceMinimum.minimum source).toList
  | .occurrence key => .occurrence token (known key).join
  | .map _ inner => .map (shape token known inner)
  | .pay inner => .pay (shape token known inner)
  | .choice left right => .choice (shape token known left) (shape token known right)
  | .ap functions arguments => .product (shape token known functions) (shape token known arguments)

/-- Removing the key-presence layer preserves the choice's actual minimum. -/
theorem join_minimum (left right : Option (Option Nat)) :
    (GroupedProbe.join left right).join = MinimumSize.best left.join right.join := by
  cases left with
  | none => cases right <;> rfl
  | some left => cases right with
      | none => cases left <;> rfl
      | some right => rfl

/-- An unavailable or empty product operand has no finite minimum. -/
theorem product_minimum (left right : Option (Option Nat)) :
    (GroupedMinimum.productEntry left right).join = RecursionProbe.productMinimum left.join right.join := by
  cases left <;> cases right <;> simp [GroupedMinimum.productEntry, RecursionProbe.productMinimum]

/-- Probe erasure preserves the minimum used by every positive-sibling guard. -/
theorem shape_minimum (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root α) :
    (OccurrenceGuard.summary (shape token known recipe)).minimum =
      (GroupedMinimum.evaluate (minimumExpr recipe) known).join := by
  induction recipe with
  | finite source | retained mass positive source =>
      change (SourceMinimum.minimum source).toList.min? = (some (SourceMinimum.minimum source).toList.min?).join
      rfl
  | occurrence key => rfl
  | map transform inner ih => exact ih
  | pay inner ih =>
      simp only [shape, OccurrenceGuard.summary, minimumExpr, GroupedMinimum.evaluate, ih]
      cases GroupedMinimum.evaluate (minimumExpr inner) known <;> rfl
  | choice left right ihl ihr =>
      simp only [shape, OccurrenceGuard.summary, minimumExpr, GroupedMinimum.evaluate, join_minimum, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp only [shape, OccurrenceGuard.summary, minimumExpr, GroupedMinimum.evaluate, product_minimum, ihf, iha]

/-- The source size-unguarded token test is the exact keyed class guard. -/
theorem size_guard_exact (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root α) :
    guarded recipe known = true ↔ token ∉ (OccurrenceGuard.summary (shape token known recipe)).unguarded := by
  induction recipe with
  | finite source | retained mass positive source => simp [guarded, shape, OccurrenceGuard.summary]
  | occurrence key => simp [guarded, shape, OccurrenceGuard.summary]
  | map transform inner ih => exact ih
  | pay inner ih => simp [guarded, shape, OccurrenceGuard.summary]
  | choice left right ihl ihr =>
      simp [guarded, shape, OccurrenceGuard.summary, OccurrenceGuard.union, Bool.and_eq_true, ihl, ihr]
  | ap functions arguments ihf iha =>
      by_cases leftZero : (GroupedMinimum.evaluate (minimumExpr functions) known).join = some 0 <;>
        by_cases rightZero : (GroupedMinimum.evaluate (minimumExpr arguments) known).join = some 0 <;>
        simp [guarded, shape, OccurrenceGuard.summary, OccurrenceGuard.union, OccurrenceGuard.beside,
          shape_minimum, leftZero, rightZero, Bool.and_eq_true, ihf, iha]

/-- Pay changes size but does not remove the source termless token. -/
def termGuard : Recipe Key Root α → Bool
  | .finite _ | .retained .. => true
  | .occurrence _ => false
  | .map _ inner | .pay inner => termGuard inner
  | .choice left right => termGuard left && termGuard right
  | .ap .. => true

theorem term_guard_exact (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root α) :
    termGuard recipe = true ↔ token ∉ (OccurrenceGuard.summary (shape token known recipe)).termless := by
  induction recipe with
  | finite source | retained mass positive source => simp [termGuard, shape, OccurrenceGuard.summary]
  | occurrence key => simp [termGuard, shape, OccurrenceGuard.summary]
  | map transform inner ih | pay inner ih => exact ih
  | choice left right ihl ihr =>
      simp [termGuard, shape, OccurrenceGuard.summary, OccurrenceGuard.union, Bool.and_eq_true, ihl, ihr]
  | ap functions arguments ihf iha => simp [termGuard, shape, OccurrenceGuard.summary]

/-- The combined source rejection reads both token sets. -/
def unguarded (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root α) : Prop :=
  token ∈ (OccurrenceGuard.summary (shape token known recipe)).unguarded ∨
    token ∈ (OccurrenceGuard.summary (shape token known recipe)).termless

theorem accepted_guards (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root α) :
    ¬unguarded token known recipe ↔ guarded recipe known = true ∧ termGuard recipe = true := by
  rw [size_guard_exact token known recipe, term_guard_exact token known recipe]
  exact not_or

/-- Every key that passes the public check discharges the semantic class guard. -/
theorem family_guards (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root)
    (accepted : ∀ key, ¬unguarded token (minima keys complete program) (program key)) :
    ∀ key, guarded (program key) (minima keys complete program) = true :=
  fun key => ((accepted_guards token _ _).mp (accepted key)).1

/-- The family is used if any body subexpression reads a keyed occurrence. -/
def used : Recipe Key Root α → Bool
  | .finite _ | .retained .. => false
  | .occurrence _ => true
  | .map _ inner | .pay inner => used inner
  | .choice left right | .ap left right => used left || used right

/-- The source's finite shortcut reads exactly the computed used-token set. -/
theorem used_exact (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root α) :
    used recipe = true ↔ token ∈ (OccurrenceGuard.summary (shape token known recipe)).used := by
  induction recipe with
  | finite source | retained mass positive source => simp [used, shape, OccurrenceGuard.summary]
  | occurrence key => simp [used, shape, OccurrenceGuard.summary]
  | map transform inner ih | pay inner ih => exact ih
  | choice left right ihl ihr | ap left right ihl ihr =>
      simp [used, shape, OccurrenceGuard.summary, OccurrenceGuard.union, Bool.or_eq_true, ihl, ihr]

/-- Size descent alone does not claim that the public term-growth check accepts. -/
theorem paid_occurrence (token : Nat) (known : GroupedProbe.Table Key) (key : Key) :
    guarded (Recipe.pay (.occurrence (Root := Root) key)) known = true ∧
      unguarded token known (Recipe.pay (.occurrence (Root := Root) key)) := by
  simp [guarded, unguarded, shape, OccurrenceGuard.summary]

end MicroCFTA.KeyedGuards
