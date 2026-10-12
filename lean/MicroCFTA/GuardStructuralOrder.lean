import MicroCFTA.FormulaStructuralOrder
import MicroCFTA.GuardConjunction

/-!
# Source guard order and canonical conjunction

The source derives Ord in constructor and field declaration order. Paths
compare their child-index lists. This model uses nonnegative child indexes.
-/
namespace MicroCFTA.GuardStructuralOrder
open SourceGuards FullSyntax StructuralOrder FormulaStructuralOrder

/-- A path retains its lexicographic child-index order. -/
def pathKey (path : Path) : Key := .node 0 (path.map Key.nat)

/-- A substitution compares its actual path before its formal path. -/
def substitutionKey (s : Substitution) : Key := .node 0 [pathKey s.actual, pathKey s.formal]

/-- Source declaration order of every guard constructor. -/
def tag : Guard Formula → Nat
  | .top => 0 | .bottom => 1 | .same _ _ => 2 | .entails _ _ => 3
  | .satisfies _ _ => 4 | .holds _ _ => 5 | .substitute _ _ => 6
  | .not _ => 7 | .and _ => 8 | .or _ => 9

/-- The complete guard key preserves constructor tags and every ordered field. -/
def guardKey : Guard Formula → Key
  | .top => .node 0 []
  | .bottom => .node 1 []
  | .same p q => .node 2 [pathKey p, pathKey q]
  | .entails p q => .node 3 [pathKey p, pathKey q]
  | .satisfies p f => .node 4 [pathKey p, formulaKey f]
  | .holds ps f => .node 5 [.node 0 (ps.map pathKey), formulaKey f]
  | .substitute additions inner => .node 6 [.node 0 (additions.map substitutionKey), guardKey inner]
  | .not inner => .node 7 [guardKey inner]
  | .and parts => .node 8 [.node 0 (parts.map guardKey)]
  | .or parts => .node 9 [.node 0 (parts.map guardKey)]

/-- Ordered substitution lists retain source field order and repetitions. -/
def compareSubstitutions : List Substitution → List Substitution → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a.actual b.actual).then
      ((compare a.formal b.formal).then (compareSubstitutions as bs))

mutual
/-- The Haskell derived guard comparison, written as recursive equations. -/
def compareGuard : Guard Formula → Guard Formula → Ordering
  | .top, .top | .bottom, .bottom => .eq
  | .same a b, .same c d | .entails a b, .entails c d => (compare a c).then (compare b d)
  | .satisfies p f, .satisfies q g => (compare p q).then (FormulaOrder.compareFormula f g)
  | .holds ps f, .holds qs g => (compare ps qs).then (FormulaOrder.compareFormula f g)
  | .substitute as p, .substitute bs q => (compareSubstitutions as bs).then (compareGuard p q)
  | .not p, .not q => compareGuard p q
  | .and ps, .and qs | .or ps, .or qs => compareGuards ps qs
  | a, b => compare (tag a) (tag b)
termination_by a _ => sizeOf a

/-- List connectives compare their guards lexicographically. -/
def compareGuards : List (Guard Formula) → List (Guard Formula) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compareGuard a b).then (compareGuards as bs)
termination_by as _ => sizeOf as
end

private theorem list_encoding (key : α → Key) (cmp : α → α → Ordering)
    (exact : ∀ a b, compareKey (key a) (key b) = cmp a b) (as bs : List α) :
    compareKeys (as.map key) (bs.map key) = List.compareLex cmp as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compareKeys, List.compareLex]
  | cons a as ih => cases bs with
    | nil => simp [compareKeys, List.compareLex]
    | cons b bs => simp only [List.map_cons, compareKeys, List.compareLex_cons_cons, exact, ih]

/-- Path encoding uses the source list comparison. -/
theorem path_exact (a b : Path) : compareKey (pathKey a) (pathKey b) = compare a b := by
  simp only [pathKey, compareKey, show compare (0 : Nat) 0 = .eq from rfl, Ordering.eq_then]
  exact list_encoding Key.nat compare (fun a b => by simp only [compareKey]) a b

/-- Path lists use the source nested list comparison. -/
theorem paths_exact (a b : List Path) : compareKeys (a.map pathKey) (b.map pathKey) = compare a b :=
  list_encoding pathKey compare path_exact a b

/-- Encoded substitution lists match their source comparison. -/
theorem substitutions_exact (as bs : List Substitution) :
    compareKeys (as.map substitutionKey) (bs.map substitutionKey) = compareSubstitutions as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compareKeys, compareSubstitutions]
  | cons a as ih => cases bs <;>
      simp [compareKeys, substitutionKey, compareKey, compareSubstitutions, path_exact, ih, Ordering.then_assoc]

mutual
/-- The complete guard comparison is exactly comparison of the structural keys. -/
theorem guard_exact (a b : Guard Formula) : compareKey (guardKey a) (guardKey b) = compareGuard a b := by
  cases a with
  | top | bottom => cases b <;> simp [Nat.compare_eq_ite_lt, guardKey, compareKey, compareKeys, compareGuard, tag]
  | same p q | entails p q => cases b <;>
      simp [Nat.compare_eq_ite_lt, guardKey, compareKey, compareKeys, compareGuard, tag, path_exact]
  | satisfies p f => cases b <;>
      simp [Nat.compare_eq_ite_lt, guardKey, compareKey, compareKeys, compareGuard, tag, path_exact, formula_exact]
  | holds ps f => cases b <;>
      simp [Nat.compare_eq_ite_lt, guardKey, compareKey, compareKeys, compareGuard, tag, paths_exact, formula_exact]
  | substitute additions p => cases b <;>
      simp [Nat.compare_eq_ite_lt, guardKey, compareKey, compareKeys, compareGuard, tag, substitutions_exact, guard_exact p]
  | not p => cases b <;> simp [Nat.compare_eq_ite_lt, guardKey, compareKey, compareKeys, compareGuard, tag, guard_exact p]
  | and ps | or ps => cases b <;> simp [Nat.compare_eq_ite_lt, guardKey, compareKey, compareKeys, compareGuard, tag, guards_exact ps]
termination_by sizeOf a

/-- Encoded guard lists retain their lexicographic order. -/
theorem guards_exact (as bs : List (Guard Formula)) :
    compareKeys (as.map guardKey) (bs.map guardKey) = compareGuards as bs := by
  cases as with
  | nil => cases bs <;> simp [compareKeys, compareGuards]
  | cons a as => cases bs <;> simp [compareKeys, compareGuards, guard_exact a, guards_exact as]
termination_by sizeOf as
end

private theorem substitutions_eq (as bs : List Substitution) : compareSubstitutions as bs = .eq ↔ as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compareSubstitutions]
  | cons a as ih => cases bs with
    | nil => simp [compareSubstitutions]
    | cons b bs =>
        cases a; cases b
        simp [compareSubstitutions, ih, and_assoc]

mutual
/-- Source comparison equality identifies exactly identical guards. -/
theorem guard_eq (a b : Guard Formula) : compareGuard a b = .eq ↔ a = b := by
  cases a with
  | top | bottom | same _ _ | entails _ _ => cases b <;> simp [compareGuard, tag]
  | satisfies _ _ | holds _ _ => cases b <;> simp [compareGuard, tag, FormulaOrder.formula_eq]
  | substitute additions p => cases b <;> simp [compareGuard, tag, substitutions_eq, guard_eq p]
  | not p => cases b <;> simp [compareGuard, tag, guard_eq p]
  | and ps | or ps => cases b <;> simp [compareGuard, tag, guards_eq ps]
termination_by sizeOf a

/-- Guard list comparison equality includes order and repetitions. -/
theorem guards_eq (as bs : List (Guard Formula)) : compareGuards as bs = .eq ↔ as = bs := by
  cases as with
  | nil => cases bs <;> simp [compareGuards]
  | cons a as => cases bs <;> simp [compareGuards, guard_eq a, guards_eq as]
termination_by sizeOf as
end

/-- The actual guard comparison has transitive non-strict order. -/
instance guardTrans : Std.TransCmp compareGuard where
  eq_swap := by intro a b; rw [← guard_exact, ← guard_exact]; exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c ab bc
    rw [← guard_exact] at ab bc ⊢
    exact Std.TransCmp.isLE_trans ab bc

/-- The non-strict source order used to produce the sorted conjunction. -/
def le (a b : Guard Formula) : Bool := (compareGuard a b).isLE

theorem le_trans (a b c : Guard Formula) : le a b → le b c → le a c :=
  Std.TransCmp.isLE_trans

theorem le_total (a b : Guard Formula) : le a b || le b a := by
  unfold le
  rw [Std.OrientedCmp.eq_swap (cmp := compareGuard) (a := b)]
  cases compareGuard a b <;> rfl

theorem le_antisymm (a b : Guard Formula) (ab : le a b) (ba : le b a) : a = b := by
  apply (guard_eq a b).mp
  apply Ordering.eq_eq_of_isLE_of_isLE_swap ab
  simpa only [le, Std.OrientedCmp.eq_swap (cmp := compareGuard) (a := b)] using ba

/-- Canonical source conjunction is structurally idempotent without order-law assumptions. -/
theorem normalize_idempotent [DecidableEq (Guard Formula)] (guard : Guard Formula) :
    GuardConjunction.normalize le (GuardConjunction.normalize le guard) = GuardConjunction.normalize le guard :=
  GuardConjunction.normalize_idempotent le le_trans le_total le_antisymm guard

/-- Repeated intersections cannot append an existing source conjunct again. -/
theorem merge_absorbs [DecidableEq (Guard Formula)] (a b : Guard Formula) :
    GuardConjunction.merge le (GuardConjunction.merge le a b) a = GuardConjunction.merge le a b :=
  GuardConjunction.merge_absorbs le le_trans le_total le_antisymm a b

end MicroCFTA.GuardStructuralOrder
