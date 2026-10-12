import MicroCFTA.SourceEnclosingRenames

/-!
# Identity filtering can expose a later formal in one scope

The complete quotient turns the first replacement of a into an identity.
The source removes that entry and selects the later a-to-b replacement.
The sparse fresh replacement is not an identity and remains first.
The enclosing-scope safeguard does not inspect this same-scope change.
-/
namespace MicroCFTA.SameScopeIdentityCapture
open SourceGuards SourceObservations FullSyntax

/-- Two replacement entries use formal a; complete identity filtering removes the first. -/
def guard : Guard Formula :=
  .substitute [⟨[0], [0]⟩, ⟨[1], [4]⟩, ⟨[2], [0]⟩]
    (.satisfies [5] (NestedScopeCapture.zero "a"))

/-- The sparse table separates equal actuals; the complete table identifies them. -/
theorem tables :
    substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameShape SourceFormula.operations (observe NestedScopeCapture.term) []) guard =
      ([([0], "__microcfta_actual_0", "a"), ([1], "__microcfta_actual_1", "a")], [[0], [1]]) ∧
    substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameTerm SourceFormula.operations NestedScopeCapture.term []) guard = ([], []) := by
  have actualOrder : orderedPaths [[0], [1], [2]] = [[0], [1], [2]] := by
    change ([[0], [1], [2]] : List Path).mergeSort _ = _
    simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]
  have usedOrder : orderedPaths [[0], [0], [1], [4], [2], [0], [5]] = [[0], [1], [2], [4], [5]] := by
    change ([[0], [1], [4], [2], [5]] : List Path).mergeSort _ = _
    simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]
  constructor
  all_goals
    simp only [guard, substitutionValues, actuals, actualPaths, allocated, conflicts, values,
      usedNames, paths, requirements, ambiguous, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_nil, actualOrder, usedOrder]
  · decide +kernel
  · have same : sameTerm SourceFormula.operations NestedScopeCapture.term [] =
        (fun left right => do
          let first ← Language.Term.atPath NestedScopeCapture.term left
          let second ← Language.Term.atPath NestedScopeCapture.term right
          pure (Language.termEq first second)) := by
      funext left right
      simp only [sameTerm, ActualQuotient.renameTree_empty]
    rw [same]
    decide +kernel

private instance resolvedDecidableEq : DecidableEq (Resolved Formula) := by
  intro first second
  cases first; cases second
  exact decidable_of_iff _ (Iff.of_eq (Resolved.mk.injEq _ _ _ _ _ _ _ _ _ _).symm)

private def scope : List (Resolved Formula) :=
  [⟨("a", "__microcfta_actual_0"), ("a", "a"), NestedScopeCapture.zero "__microcfta_actual_0",
      some ("__microcfta_actual_0", "a"), false⟩,
   ⟨("y", "__microcfta_actual_1"), ("y", "a"), NestedScopeCapture.zero "__microcfta_actual_1",
      some ("__microcfta_actual_1", "a"), false⟩,
   ⟨("a", "b"), ("a", "b"), .top, none, true⟩]

private theorem assumptions :
    withActualAssumptions SourceFormula.operations [scope] .top = NestedScopeCapture.sparseAntecedent := by
  change FormulaExecutable.simplify (.and [NestedScopeCapture.zero "__microcfta_actual_0",
    NestedScopeCapture.zero "__microcfta_actual_1", .top, .top]) = _
  rw [FormulaExecutable.simplify]
  have contradiction : [NestedScopeCapture.zero "__microcfta_actual_0",
      NestedScopeCapture.zero "__microcfta_actual_1", .top, .top].any FormulaExecutable.contradiction = false := by
    decide +kernel
  rw [contradiction]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have flattened : FormulaSimplify.flatten ((FormulaExecutable.simplifyParts
      [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1", .top, .top]).filter
        (fun part => !FormulaExecutable.tautology part)) =
      [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1"] := by
    decide +kernel
  rw [flattened]
  have canonical : FormulaExecutable.canonical
      [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1"] =
      [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1"] := by
    unfold FormulaExecutable.canonical
    have erased : [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1"].eraseDups =
        [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1"] := by decide +kernel
    rw [erased]
    exact List.mergeSort_of_pairwise (by decide +kernel)
  rw [canonical]
  rfl

/-- The upstream de910ea safeguard admits the same-scope sparse Yes. -/
theorem sparse_yes :
    SourceEnclosingRenames.evaluateGuardWithShape SourceFormula.operations NestedScopeCapture.solver
      (observe NestedScopeCapture.term) guard = .yes := by
  unfold SourceEnclosingRenames.evaluateGuardWithShape
  simp only [guard, SourceEnclosingRenames.evaluate]
  unfold SourceEnclosingRenames.evaluateScoped
  change SourceEnclosingRenames.evaluateWith _ _ _ _
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameShape SourceFormula.operations (observe NestedScopeCapture.term) []) guard).1
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameShape SourceFormula.operations (observe NestedScopeCapture.term) []) guard).2 [] true guard = .yes
  rw [tables.1]
  simp only [guard, SourceEnclosingRenames.evaluateWith]
  have resolved : resolveMany SourceFormula.operations (observe NestedScopeCapture.term)
      [([0], "__microcfta_actual_0", "a"), ([1], "__microcfta_actual_1", "a")] [[0], [1]]
      [⟨[0], [0]⟩, ⟨[1], [4]⟩, ⟨[2], [0]⟩] = some scope := by decide +kernel
  rw [resolved]
  have pass : scope.any (SourceEnclosingRenames.renamedByEnclosing []) = false := by decide +kernel
  simp only [pass, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  have observed : observe NestedScopeCapture.term [5] = some ⟨"target", .top, .leaf⟩ := by decide +kernel
  rw [observed]
  dsimp only
  have applied : applySubstitutions SourceFormula.operations [scope] .top = .top := by decide +kernel
  rw [applied, assumptions]
  decide +kernel

/-- Complete evaluation rejects the term after identity filtering exposes the later replacement. -/
theorem complete_no :
    SourceEnclosingRenames.evaluateGuard SourceFormula.operations NestedScopeCapture.solver
      guard NestedScopeCapture.term = .no := by
  unfold SourceEnclosingRenames.evaluateGuard
  simp only [guard, SourceEnclosingRenames.evaluate]
  unfold SourceEnclosingRenames.evaluateScoped
  change SourceEnclosingRenames.evaluateWith _ _ _ _
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameTerm SourceFormula.operations NestedScopeCapture.term []) guard).1
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameTerm SourceFormula.operations NestedScopeCapture.term []) guard).2 [] true guard = .no
  rw [tables.2]
  simp only [guard, SourceEnclosingRenames.evaluateWith]
  decide +kernel

end MicroCFTA.SameScopeIdentityCapture
