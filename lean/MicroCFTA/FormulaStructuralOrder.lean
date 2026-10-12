import MicroCFTA.FormulaOrder
import MicroCFTA.StructuralOrder

/-!
# Total structural order of formulas

Encode constructor tags and fields in a finite ordered tree. The encoded
comparison agrees with the source comparison, including list field order.
-/
namespace MicroCFTA.FormulaStructuralOrder
open FullSyntax FormulaOrder StructuralOrder

/-- Sort fields retain their source declaration order. -/
def sortKey : ValueSort → Key
  | .int => .node 0 []
  | .real => .node 1 []
  | .bool => .node 2 []
  | .function args result => .node 3 [.node 0 (args.map sortKey), sortKey result]

/-- A binder compares its name before its sort. -/
def binderKey (binder : Name × ValueSort) : Key :=
  .node 0 [.text binder.1, sortKey binder.2]

mutual
/-- Term constructor tags and fields follow the actual structural comparison. -/
def termKey : Term → Key
  | .lit n => .node 0 [.int n]
  | .var name => .node 1 [.text name]
  | .app name args => .node 2 [.text name, .node 0 (args.map termKey)]
  | .neg t => .node 3 [termKey t]
  | .add a b => .node 4 [termKey a, termKey b]
  | .sub a b => .node 5 [termKey a, termKey b]
  | .mul a b => .node 6 [termKey a, termKey b]
  | .div a b => .node 7 [termKey a, termKey b]
  | .mod a b => .node 8 [termKey a, termKey b]
  | .ite p a b => .node 9 [formulaKey p, termKey a, termKey b]
  | .cast t s => .node 10 [termKey t, sortKey s]
termination_by t => sizeOf t

/-- Formula fields include ordered quantifier declarations before their bodies. -/
def formulaKey : Formula → Key
  | .top => .node 0 []
  | .and ps => .node 1 [.node 0 (ps.map formulaKey)]
  | .bottom => .node 2 []
  | .or ps => .node 3 [.node 0 (ps.map formulaKey)]
  | .not p => .node 4 [formulaKey p]
  | .atom r a b => .node 5 [.nat (CoreFormula.relationTag r), termKey a, termKey b]
  | .forall bound p => .node 6 [.node 0 (bound.map binderKey), formulaKey p]
  | .exists bound p => .node 7 [.node 0 (bound.map binderKey), formulaKey p]
termination_by p => sizeOf p
end

mutual
/-- Encoded sort comparison is exactly the source recursive comparison. -/
theorem sort_exact (a b : ValueSort) : compareKey (sortKey a) (sortKey b) = compareSort a b := by
  cases a with
  | int | real | bool => cases b <;> simp [Nat.compare_eq_ite_lt, sortKey, compareKey, compareKeys, compareSort, sortTag]
  | function args result =>
      cases b <;> simp [Nat.compare_eq_ite_lt, sortKey, compareKey, compareKeys, compareSort, sortTag, sorts_exact args, sort_exact result]
termination_by sizeOf a

/-- Encoding a sort list keeps lexicographic order. -/
theorem sorts_exact (as bs : List ValueSort) : compareKeys (as.map sortKey) (bs.map sortKey) = compareSorts as bs := by
  cases as with
  | nil => cases bs <;> simp [compareKeys, compareSorts]
  | cons a as => cases bs <;> simp [compareKeys, compareSorts, sort_exact a, sorts_exact as]
termination_by sizeOf as
end

/-- Binder-list comparison preserves names, sorts, and repetitions. -/
theorem binders_exact (as bs : List (Name × ValueSort)) :
    compareKeys (as.map binderKey) (bs.map binderKey) = compareBinders as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compareKeys, compareBinders]
  | cons a as ih =>
      rcases a with ⟨name, sort⟩
      cases bs with
      | nil => simp [compareKeys, compareBinders]
      | cons b bs =>
          rcases b with ⟨other, otherSort⟩
          simp [compareKeys, binderKey, compareKey, compareBinders, sort_exact, ih, Ordering.then_assoc]

mutual
/-- All term constructors have exactly the encoded structural order. -/
theorem term_exact (a b : Term) : compareKey (termKey a) (termKey b) = compareTerm a b := by
  cases a with
  | lit n | var n => cases b <;> simp [Nat.compare_eq_ite_lt, termKey, compareKey, compareKeys, compareTerm, termTag]
  | app n ts => cases b <;> simp [Nat.compare_eq_ite_lt, termKey, compareKey, compareKeys, compareTerm, termTag, terms_exact ts]
  | neg t => cases b <;> simp [Nat.compare_eq_ite_lt, termKey, compareKey, compareKeys, compareTerm, termTag, term_exact t]
  | add t u | sub t u | mul t u | div t u | mod t u =>
      cases b <;> simp [Nat.compare_eq_ite_lt, termKey, compareKey, compareKeys, compareTerm, termTag, term_exact t, term_exact u]
  | ite p t u => cases b <;> simp [Nat.compare_eq_ite_lt, termKey, compareKey, compareKeys, compareTerm, termTag, formula_exact p, term_exact t, term_exact u]
  | cast t s => cases b <;> simp [Nat.compare_eq_ite_lt, termKey, compareKey, compareKeys, compareTerm, termTag, term_exact t, sort_exact s]
termination_by sizeOf a

/-- Encoding term lists preserves their ordered comparison. -/
theorem terms_exact (as bs : List Term) : compareKeys (as.map termKey) (bs.map termKey) = compareTerms as bs := by
  cases as with
  | nil => cases bs <;> simp [compareKeys, compareTerms]
  | cons a as => cases bs <;> simp [compareKeys, compareTerms, term_exact a, terms_exact as]
termination_by sizeOf as

/-- All formula constructors have exactly the encoded structural order. -/
theorem formula_exact (a b : Formula) : compareKey (formulaKey a) (formulaKey b) = compareFormula a b := by
  cases a with
  | top | bottom => cases b <;> simp [Nat.compare_eq_ite_lt, formulaKey, compareKey, compareKeys, compareFormula, formulaTag]
  | and ps | or ps => cases b <;> simp [Nat.compare_eq_ite_lt, formulaKey, compareKey, compareKeys, compareFormula, formulaTag, parts_exact ps]
  | not p => cases b <;> simp [Nat.compare_eq_ite_lt, formulaKey, compareKey, compareKeys, compareFormula, formulaTag, formula_exact p]
  | atom r t u => cases b <;> simp [Nat.compare_eq_ite_lt, formulaKey, compareKey, compareKeys, compareFormula, formulaTag, term_exact t, term_exact u]
  | «forall» bound p | «exists» bound p =>
      cases b <;> simp [Nat.compare_eq_ite_lt, formulaKey, compareKey, compareKeys, compareFormula, formulaTag, binders_exact bound, formula_exact p]
termination_by sizeOf a

/-- Encoding formula lists preserves their ordered comparison. -/
theorem parts_exact (as bs : List Formula) : compareKeys (as.map formulaKey) (bs.map formulaKey) = compareParts as bs := by
  cases as with
  | nil => cases bs <;> simp [compareKeys, compareParts]
  | cons a as => cases bs <;> simp [compareKeys, compareParts, formula_exact a, parts_exact as]
termination_by sizeOf as
end

/-- The complete formula comparator is transitive and reverses on swapped inputs. -/
instance formulaTrans : Std.TransCmp compareFormula where
  eq_swap := by intro a b; rw [← formula_exact, ← formula_exact]; exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c ab bc
    rw [← formula_exact] at ab bc ⊢
    exact Std.TransCmp.isLE_trans ab bc

end MicroCFTA.FormulaStructuralOrder
