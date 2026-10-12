import MicroCFTA.SourceIdentityMap

/-!
# Sparse actual names hide capture by an outer substitution

Two equal inner actuals receive distinct sparse names. Complete evaluation
uses their one ambient name. An outer substitution changes only that ambient
name, so a sparse positive query need not remain true for the complete term.
-/
namespace MicroCFTA.NestedScopeCapture
open SourceGuards SourceObservations FullSyntax

private instance resolvedDecidableEq : DecidableEq (Resolved Formula) := by
  intro first second
  cases first; cases second
  exact decidable_of_iff _ (Iff.of_eq (Resolved.mk.injEq _ _ _ _ _ _ _ _ _ _).symm)

/-- A free name is zero. -/
def zero (name : String) : Formula := .atom .eq (.var name) (.lit 0)

/-- The exact sparse query can prove the first of its two ambient actual assumptions. -/
def sparseAntecedent : Formula := .and [zero "__microcfta_actual_0", zero "__microcfta_actual_1"]

/-- This pure callback decides just the two witness queries. -/
def solver : SourceGuards.Entailment Formula := fun _ antecedent consequent =>
  if antecedent = sparseAntecedent && consequent = zero "__microcfta_actual_0" then .yes
  else if antecedent = zero "a" && consequent = zero "b" then .no else .unknown

/-- The callback's positive result is valid; its negative result has the concrete a=0,b=1 countermodel. -/
theorem solver_sound : SourceEntailment.Sound integerModel (fun _ _ => True) solver := by
  intro bindings antecedent consequent
  unfold solver
  split
  · rename_i positive
    have same := Bool.and_eq_true_iff.mp positive
    have left : antecedent = sparseAntecedent := by simpa using same.1
    have right : consequent = zero "__microcfta_actual_0" := by simpa using same.2
    subst antecedent; subst consequent
    intro env _ assumed
    simp only [sparseAntecedent, Holds, holdsAll] at assumed
    exact assumed.1
  · split
    · rename_i negative
      have same := Bool.and_eq_true_iff.mp negative
      have left : antecedent = zero "a" := by simpa using same.1
      have right : consequent = zero "b" := by simpa using same.2
      subst antecedent; subst consequent
      intro proved
      have impossible := proved (fun name => if name = "b" then 1 else 0) True.intro
        (by simp [zero, Holds, evaluateTerm, integerModel, CoreFormula.evalRelation])
      simp [zero, Holds, evaluateTerm, integerModel, CoreFormula.evalRelation] at impossible
    · trivial

/-- The source scope order puts the a-to-b substitution outside the x-to-actual substitution. -/
def guard : SourceGuards.Guard Formula :=
  .substitute [⟨[2], [0]⟩]
    (.substitute [⟨[0], [3]⟩, ⟨[1], [4]⟩] (.satisfies [5] (zero "x")))

/-- The two a actuals are equal inner terms. -/
def term : Language.Term (Label Formula) :=
  let leaf := fun name => Language.Term.node (name, Formula.top) []
  let actual := Language.Term.node ("a", zero valueName) [leaf "z"]
  .node ("root", .top) [actual, actual, leaf "b", leaf "x", leaf "y", leaf "target"]

private theorem actual_order : orderedPaths [[2], [0], [1]] = [[0], [1], [2]] := by
  change ([[2], [0], [1]] : List Path).mergeSort _ = _
  simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]

private theorem used_order : orderedPaths [[2], [0], [0], [3], [1], [4], [5]] = [[0], [1], [2], [3], [4], [5]] := by
  change ([[2], [0], [3], [1], [4], [5]] : List Path).mergeSort _ = _
  simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]

private theorem complete_same : sameTerm SourceFormula.operations term [] =
    (fun left right => do
      let first ← Language.Term.atPath term left
      let second ← Language.Term.atPath term right
      pure (Language.termEq first second)) := by
  funext left right
  simp only [sameTerm, ActualQuotient.renameTree_empty]

private theorem canonical_sparse :
    FormulaExecutable.canonical [zero "__microcfta_actual_0", zero "__microcfta_actual_1"] =
      [zero "__microcfta_actual_0", zero "__microcfta_actual_1"] := by
  unfold FormulaExecutable.canonical
  have erased : [zero "__microcfta_actual_0", zero "__microcfta_actual_1"].eraseDups =
      [zero "__microcfta_actual_0", zero "__microcfta_actual_1"] := by decide +kernel
  rw [erased]
  exact List.mergeSort_of_pairwise (by decide +kernel)

/-- The sparse pass creates two ambiguous names; the complete pass merges them into ambient a. -/
theorem tables :
    substitutionValues SourceFormula.operations (observe term) (sameShape SourceFormula.operations (observe term) []) guard =
      ([([0], "__microcfta_actual_0", "a"), ([1], "__microcfta_actual_1", "a")], [[0], [1]]) ∧
    substitutionValues SourceFormula.operations (observe term) (sameTerm SourceFormula.operations term []) guard = ([], []) := by
  rw [complete_same]
  constructor
  all_goals
    simp only [guard, substitutionValues, actuals, actualPaths, allocated, conflicts, values,
      usedNames, paths, requirements, ambiguous, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_nil, actual_order, used_order]
  · decide +kernel
  · decide +kernel

private def outer : Resolved Formula := ⟨("a", "b"), ("a", "b"), .top, none, true⟩
private def first : Resolved Formula :=
  ⟨("x", "__microcfta_actual_0"), ("x", "a"), zero "__microcfta_actual_0", some ("__microcfta_actual_0", "a"), false⟩
private def second : Resolved Formula :=
  ⟨("y", "__microcfta_actual_1"), ("y", "a"), zero "__microcfta_actual_1", some ("__microcfta_actual_1", "a"), false⟩

private theorem sparse_assumptions :
    withActualAssumptions SourceFormula.operations [[first, second], [outer]] .top = sparseAntecedent := by
  change FormulaExecutable.simplify (.and [zero "__microcfta_actual_0", zero "__microcfta_actual_1", .top, .top]) = _
  rw [FormulaExecutable.simplify]
  have contradiction : [zero "__microcfta_actual_0", zero "__microcfta_actual_1", .top, .top].any FormulaExecutable.contradiction = false := by
    decide +kernel
  rw [contradiction]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have flattened : FormulaSimplify.flatten ((FormulaExecutable.simplifyParts
      [zero "__microcfta_actual_0", zero "__microcfta_actual_1", .top, .top]).filter
        (fun part => !FormulaExecutable.tautology part)) = [zero "__microcfta_actual_0", zero "__microcfta_actual_1"] := by
    decide +kernel
  rw [flattened, canonical_sparse]
  rfl

/-- A sound callback confirms the sparse guard and rejects the public complete guard. -/
theorem verdicts :
    evaluateGuardWithShape SourceFormula.operations solver (observe term) guard = .yes ∧
      evaluateGuard SourceFormula.operations solver guard term = .no := by
  constructor
  · unfold evaluateGuardWithShape evaluateGuardWithSame
    rw [tables.1]
    simp only [guard, evaluateWith]
    have out : resolveMany SourceFormula.operations (observe term)
        [([0], "__microcfta_actual_0", "a"), ([1], "__microcfta_actual_1", "a")] [[0], [1]] [⟨[2], [0]⟩] = some [outer] := by decide +kernel
    have inn : resolveMany SourceFormula.operations (observe term)
        [([0], "__microcfta_actual_0", "a"), ([1], "__microcfta_actual_1", "a")] [[0], [1]] [⟨[0], [3]⟩, ⟨[1], [4]⟩] = some [first, second] := by decide +kernel
    rw [out, inn]
    have observed : observe term [5] = some ⟨"target", .top, .leaf⟩ := by decide +kernel
    rw [observed]
    dsimp only
    have applied : applySubstitutions SourceFormula.operations [[first, second], [outer]] .top = .top := by decide +kernel
    rw [applied, sparse_assumptions]
    decide +kernel
  · unfold evaluateGuard evaluateGuardWithSame
    rw [tables.2]
    simp only [guard, evaluateWith]
    decide +kernel

end MicroCFTA.NestedScopeCapture
