import MicroCFTA.FormulaSimplify

/-!
# Structural comparison of the complete formula syntax

The comparison follows the Haskell derived `Ord` constructor order and then
compares fields lexicographically. Equality of comparison results agrees with
structural equality. Thus ordered-set duplicate removal uses the same equality
as the simplifier model.
-/

namespace MicroCFTA.FormulaOrder

open FullSyntax

/-- Source declaration order of sorts. -/
def sortTag : ValueSort → Nat
  | .int => 0 | .real => 1 | .bool => 2 | .function _ _ => 3

mutual
/-- Derived sort comparison, including each function argument and result. -/
def compareSort : ValueSort → ValueSort → Ordering
  | .function as a, .function bs b => (compareSorts as bs).then (compareSort a b)
  | a, b => compare (sortTag a) (sortTag b)
termination_by a _ => sizeOf a

/-- Function signatures compare their argument lists lexicographically. -/
def compareSorts : List ValueSort → List ValueSort → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compareSort a b).then (compareSorts as bs)
termination_by as _ => sizeOf as
end

/-- Binder lists compare each name before its sort, in source list order. -/
def compareBinders : List (Name × ValueSort) → List (Name × ValueSort) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (an, aSort) :: as, (bn, bSort) :: bs =>
      (compare an bn).then ((compareSort aSort bSort).then (compareBinders as bs))

/-- Source declaration order of full terms. -/
def termTag : Term → Nat
  | .lit _ => 0 | .var _ => 1 | .app _ _ => 2 | .neg _ => 3 | .add _ _ => 4
  | .sub _ _ => 5 | .mul _ _ => 6 | .div _ _ => 7 | .mod _ _ => 8
  | .ite _ _ _ => 9 | .cast _ _ => 10

/-- Source declaration order of full formulas. -/
def formulaTag : Formula → Nat
  | .top => 0 | .and _ => 1 | .bottom => 2 | .or _ => 3 | .not _ => 4
  | .atom _ _ _ => 5 | .forall _ _ => 6 | .exists _ _ => 7

mutual
/-- Derived term comparison follows each source constructor's field order. -/
def compareTerm : Term → Term → Ordering
  | .lit a, .lit b => compare a b
  | .var a, .var b => compare a b
  | .app a as, .app b bs => (compare a b).then (compareTerms as bs)
  | .neg a, .neg b => compareTerm a b
  | .add a b, .add c d | .sub a b, .sub c d | .mul a b, .mul c d |
      .div a b, .div c d | .mod a b, .mod c d => (compareTerm a c).then (compareTerm b d)
  | .ite p a b, .ite q c d => (compareFormula p q).then ((compareTerm a c).then (compareTerm b d))
  | .cast a s, .cast b t => (compareTerm a b).then (compareSort s t)
  | a, b => compare (termTag a) (termTag b)
termination_by a _ => sizeOf a

/-- Derived application argument comparison is lexicographic. -/
def compareTerms : List Term → List Term → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compareTerm a b).then (compareTerms as bs)
termination_by as _ => sizeOf as

/-- Derived formula comparison includes quantifier binder lists before their bodies. -/
def compareFormula : Formula → Formula → Ordering
  | .top, .top | .bottom, .bottom => .eq
  | .and ps, .and qs | .or ps, .or qs => compareParts ps qs
  | .not p, .not q => compareFormula p q
  | .atom r a b, .atom s c d => (compare (CoreFormula.relationTag r) (CoreFormula.relationTag s)).then
      ((compareTerm a c).then (compareTerm b d))
  | .forall as p, .forall bs q | .exists as p, .exists bs q =>
      (compareBinders as bs).then (compareFormula p q)
  | p, q => compare (formulaTag p) (formulaTag q)
termination_by p _ => sizeOf p

/-- Boolean list part comparison retains source order and repetitions. -/
def compareParts : List Formula → List Formula → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | p :: ps, q :: qs => (compareFormula p q).then (compareParts ps qs)
termination_by ps _ => sizeOf ps
end

mutual
/-- Sort comparison equality is exactly structural equality. -/
theorem sort_eq (a b : ValueSort) : compareSort a b = .eq ↔ a = b := by
  cases a with
  | int | real | bool => cases b <;> simp [compareSort, sortTag]
  | function as a => cases b <;> simp [compareSort, sortTag, sorts_eq as, sort_eq a]
termination_by sizeOf a

/-- Function signature list equality is exact. -/
theorem sorts_eq (as bs : List ValueSort) : compareSorts as bs = .eq ↔ as = bs := by
  cases as with
  | nil => cases bs <;> simp [compareSorts]
  | cons a as => cases bs <;> simp [compareSorts, sort_eq a, sorts_eq as]
termination_by sizeOf as
end

/-- Binder comparison equality retains every name, sort, order, and repetition. -/
theorem binders_eq (as bs : List (Name × ValueSort)) : compareBinders as bs = .eq ↔ as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compareBinders]
  | cons a as ih =>
      rcases a with ⟨an, aSort⟩
      cases bs with
      | nil => simp [compareBinders]
      | cons b bs => rcases b with ⟨bn, bSort⟩; simp [compareBinders, sort_eq, ih, and_assoc]

/-- Relation constructor tags are injective. -/
theorem relation_eq (a b : Relation) : CoreFormula.relationTag a = CoreFormula.relationTag b ↔ a = b := by
  cases a <;> cases b <;> decide

mutual
/-- Full term comparison equality is exactly structural equality. -/
theorem term_eq (a b : Term) : compareTerm a b = .eq ↔ a = b := by
  cases a with
  | lit n | var n => cases b <;> simp [compareTerm, termTag]
  | app n ts => cases b <;> simp [compareTerm, termTag, terms_eq ts]
  | neg t => cases b <;> simp [compareTerm, termTag, term_eq t]
  | add t u | sub t u | mul t u | div t u | mod t u =>
      cases b <;> simp [compareTerm, termTag, term_eq t, term_eq u]
  | ite p t u => cases b <;> simp [compareTerm, termTag, formula_eq p, term_eq t, term_eq u]
  | cast t s => cases b <;> simp [compareTerm, termTag, term_eq t, sort_eq s]
termination_by sizeOf a

/-- Term list comparison equality is exact. -/
theorem terms_eq (as bs : List Term) : compareTerms as bs = .eq ↔ as = bs := by
  cases as with
  | nil => cases bs <;> simp [compareTerms]
  | cons a as => cases bs <;> simp [compareTerms, term_eq a, terms_eq as]
termination_by sizeOf as

/-- Full formula comparison equality is exactly structural equality. -/
theorem formula_eq (p q : Formula) : compareFormula p q = .eq ↔ p = q := by
  cases p with
  | top | bottom => cases q <;> simp [compareFormula, formulaTag]
  | and ps | or ps => cases q <;> simp [compareFormula, formulaTag, parts_eq ps]
  | not p => cases q <;> simp [compareFormula, formulaTag, formula_eq p]
  | atom r t u => cases q <;> simp [compareFormula, formulaTag, term_eq t, term_eq u, relation_eq]
  | «forall» bound p | «exists» bound p => cases q <;> simp [compareFormula, formulaTag, binders_eq bound, formula_eq p]
termination_by sizeOf p

/-- Formula list comparison equality is exact. -/
theorem parts_eq (ps qs : List Formula) : compareParts ps qs = .eq ↔ ps = qs := by
  cases ps with
  | nil => cases qs <;> simp [compareParts]
  | cons p ps => cases qs <;> simp [compareParts, formula_eq p, parts_eq ps]
termination_by sizeOf ps
end

/-- The full source constructor order instantiates the general simplifier. -/
noncomputable def simplify (formula : Formula) : Formula :=
  FormulaSimplify.simplify (fun p q => (compareFormula p q).isLE) formula

/-- Simplification with the actual source constructor comparison preserves truth. -/
theorem simplify_semantics (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (env : Name → Value) (formula : Formula) : Holds model env (simplify formula) ↔ Holds model env formula :=
  FormulaSimplify.simplify_semantics model laws env _ formula

end MicroCFTA.FormulaOrder
