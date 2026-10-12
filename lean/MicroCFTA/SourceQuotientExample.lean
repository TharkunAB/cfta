import MicroCFTA.SourceQuotientGuards

/-!
# An accepted ambiguous source query

Two equal non-leaf actuals have separate sparse declarations and one complete
ambient name. Both runtime scope checks pass. The sparse callback says Yes;
the complete logical query follows from the general quotient theorem.
The same sound callback may still answer Unknown on the complete spelling.
-/
namespace MicroCFTA.SourceQuotientExample
open FullSyntax SourceFormula SourceObservations SourceQuotientEnvironment SourceQuotientQueries
open SourceGuards (Path Guard Resolved)

/-- A single scope substitutes the two equal actuals for distinct formals. -/
def recipe : Recipe := [⟨[0], [3]⟩, ⟨[1], [4]⟩]

/-- The requirement reads the first substituted value. -/
def guard : Guard Formula := .substitute recipe (.satisfies [5] (NestedScopeCapture.zero "x"))

/-- The sparse source resolves two fresh identities. -/
def sparse : Scope :=
  [⟨("x", "__microcfta_actual_0"), ("x", "a"), NestedScopeCapture.zero "__microcfta_actual_0",
      some ("__microcfta_actual_0", "a"), false⟩,
   ⟨("y", "__microcfta_actual_1"), ("y", "a"), NestedScopeCapture.zero "__microcfta_actual_1",
      some ("__microcfta_actual_1", "a"), false⟩]

/-- Complete source resolution drops both fresh declarations. -/
def complete : Scope :=
  [⟨("x", "a"), ("x", "a"), NestedScopeCapture.zero "a", none, true⟩,
   ⟨("y", "a"), ("y", "a"), NestedScopeCapture.zero "a", none, true⟩]

private instance resolvedDecidableEq : DecidableEq (Resolved Formula) := by
  intro first second
  cases first; cases second
  exact decidable_of_iff _ (Iff.of_eq (Resolved.mk.injEq _ _ _ _ _ _ _ _ _ _).symm)

/-- The source allocates ambiguous sparse values and no complete fresh values. -/
theorem tables :
    SourceGuards.substitutionValues operations (observe NestedScopeCapture.term)
      (sameShape operations (observe NestedScopeCapture.term) []) guard =
      ([([0], "__microcfta_actual_0", "a"), ([1], "__microcfta_actual_1", "a")], [[0], [1]]) ∧
    SourceGuards.substitutionValues operations (observe NestedScopeCapture.term)
      (sameTerm operations NestedScopeCapture.term []) guard = ([], []) := by
  have actualOrder : SourceGuards.orderedPaths [[0], [1]] = [[0], [1]] := by
    change ([[0], [1]] : List Path).mergeSort _ = _
    simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]
  have usedOrder : SourceGuards.orderedPaths [[0], [3], [1], [4], [5]] = [[0], [1], [3], [4], [5]] := by
    change ([[0], [3], [1], [4], [5]] : List Path).mergeSort _ = _
    simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]
  constructor
  all_goals
    simp only [guard, recipe, SourceGuards.substitutionValues, SourceGuards.actuals, SourceGuards.actualPaths,
      SourceGuards.allocated, SourceGuards.conflicts, SourceGuards.values, SourceGuards.usedNames,
      SourceGuards.paths, SourceGuards.requirements, SourceGuards.ambiguous,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_nil, actualOrder, usedOrder]
  · decide +kernel
  · have same : sameTerm operations NestedScopeCapture.term [] =
        (fun left right => do
          let first ← Language.Term.atPath NestedScopeCapture.term left
          let second ← Language.Term.atPath NestedScopeCapture.term right
          pure (Language.termEq first second)) := by
      funext left right
      simp only [sameTerm, ActualQuotient.renameTree_empty]
    rw [same]
    decide +kernel

/-- Both sparse and complete scopes are exact successful source resolutions. -/
theorem resolutions :
    resolve NestedScopeCapture.term guard (sameShape operations (observe NestedScopeCapture.term) []) recipe = some sparse ∧
    resolve NestedScopeCapture.term guard (sameTerm operations NestedScopeCapture.term []) recipe = some complete := by
  constructor
  · unfold resolve
    rw [tables.1]
    decide +kernel
  · unfold resolve
    rw [tables.2]
    decide +kernel

/-- Ambiguity does not itself reject this source scope. -/
theorem accepted : Accepted [sparse] := by
  simp only [Accepted]
  decide +kernel

/-- The scopes and their requested paths instantiate the general transport theorem. -/
theorem stacks :
    Resolves NestedScopeCapture.term guard (sameShape operations (observe NestedScopeCapture.term) []) [recipe] [sparse] ∧
    Resolves NestedScopeCapture.term guard (sameTerm operations NestedScopeCapture.term []) [recipe] [complete] := by
  have requested : Requested guard recipe := by
    intro entry member
    simp only [recipe, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [guard, recipe, SourceGuards.actualPaths, SourceGuards.paths]
  exact ⟨.cons ⟨resolutions.1, requested⟩ .nil, .cons ⟨resolutions.2, requested⟩ .nil⟩

private theorem sparse_assumptions :
    SourceGuards.withActualAssumptions operations [sparse] .top = NestedScopeCapture.sparseAntecedent := by
  change FormulaExecutable.simplify (.and [NestedScopeCapture.zero "__microcfta_actual_0",
    NestedScopeCapture.zero "__microcfta_actual_1", .top]) = _
  rw [FormulaExecutable.simplify]
  have contradiction : [NestedScopeCapture.zero "__microcfta_actual_0",
      NestedScopeCapture.zero "__microcfta_actual_1", .top].any FormulaExecutable.contradiction = false := by decide +kernel
  rw [contradiction]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have flattened : FormulaSimplify.flatten ((FormulaExecutable.simplifyParts
      [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1", .top]).filter
        (fun part => !FormulaExecutable.tautology part)) =
      [NestedScopeCapture.zero "__microcfta_actual_0", NestedScopeCapture.zero "__microcfta_actual_1"] := by decide +kernel
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

/-- The exact sparse source query receives Yes from the previously proved sound callback. -/
theorem query_yes :
    SourceGuards.decideWith NestedScopeCapture.solver [] [sparse]
      (SourceGuards.withActualAssumptions operations [sparse] (SourceGuards.applySubstitutions operations [sparse] .top))
      (SourceGuards.applySubstitutions operations [sparse] (NestedScopeCapture.zero "x")) = .yes := by
  have top : SourceGuards.applySubstitutions operations [sparse] .top = .top := by decide +kernel
  rw [top, sparse_assumptions]
  decide +kernel

/-- The repaired runtime accepts this ambiguous query. -/
theorem sparse_yes :
    SourceSubstitutionPrecedence.evaluateGuardWithShape operations NestedScopeCapture.solver
      (observe NestedScopeCapture.term) guard = .yes := by
  unfold SourceSubstitutionPrecedence.evaluateGuardWithShape
  simp only [guard, recipe, SourceSubstitutionPrecedence.evaluate]
  unfold SourceSubstitutionPrecedence.evaluateScoped
  change SourceSubstitutionPrecedence.evaluateWith _ _ _ _
    (SourceGuards.substitutionValues operations (observe NestedScopeCapture.term)
      (sameShape operations (observe NestedScopeCapture.term) []) guard).1
    (SourceGuards.substitutionValues operations (observe NestedScopeCapture.term)
      (sameShape operations (observe NestedScopeCapture.term) []) guard).2 [] true guard = .yes
  rw [tables.1]
  have resolved := resolutions.1
  unfold resolve at resolved
  rw [tables.1] at resolved
  simp only [guard, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, resolved]
  have passes : (sparse.any (SourceEnclosingRenames.renamedByEnclosing []) ||
      SourceSubstitutionPrecedence.ambiguousIdentityPrecedence sparse) = false := by decide +kernel
  simp only [passes, Bool.false_eq_true, ↓reduceIte]
  have observed : observe NestedScopeCapture.term [5] = some ⟨"target", .top, .leaf⟩ := by decide +kernel
  rw [observed]
  exact query_yes

/-- A sound callback can answer Unknown on the complete spelling of a logically valid query. -/
theorem complete_unknown :
    SourceSubstitutionPrecedence.evaluateGuard operations NestedScopeCapture.solver guard NestedScopeCapture.term = .unknown := by
  unfold SourceSubstitutionPrecedence.evaluateGuard
  simp only [guard, recipe, SourceSubstitutionPrecedence.evaluate]
  unfold SourceSubstitutionPrecedence.evaluateScoped
  change SourceSubstitutionPrecedence.evaluateWith _ _ _ _
    (SourceGuards.substitutionValues operations (observe NestedScopeCapture.term)
      (sameTerm operations NestedScopeCapture.term []) guard).1
    (SourceGuards.substitutionValues operations (observe NestedScopeCapture.term)
      (sameTerm operations NestedScopeCapture.term []) guard).2 [] true guard = .unknown
  rw [tables.2]
  simp only [guard, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith]
  decide +kernel

private theorem integer_laws : FormulaSimplify.RelationLaws integerModel := by
  constructor <;> intros <;> simp_all [integerModel, CoreFormula.evalRelation]

/-- The general quotient theorem certifies the complete logical query despite the callback's Unknown. -/
theorem logical_complete :
    SourceEntailment.Entails integerModel (fun _ => True)
      (SourceGuards.withActualAssumptions operations [complete]
        (SourceGuards.applySubstitutions operations [complete] .top))
      (SourceGuards.applySubstitutions operations [complete] (NestedScopeCapture.zero "x")) := by
  have proved := SourceEntailment.decideWith_sound integerModel (fun _ _ => True)
    NestedScopeCapture.solver NestedScopeCapture.solver_sound [] [sparse]
    (SourceGuards.withActualAssumptions operations [sparse] (SourceGuards.applySubstitutions operations [sparse] .top))
    (SourceGuards.applySubstitutions operations [sparse] (NestedScopeCapture.zero "x"))
  rw [query_yes] at proved
  apply entails_yes_unrestricted integerModel (by intro value; rfl) integer_laws NestedScopeCapture.term guard
    [recipe] [sparse] [complete] stacks.1 stacks.2 accepted .top (NestedScopeCapture.zero "x")
  · simp [formulaNames]
  · intro name member
    exact SourceSemanticNames.ambient_used operations (observe NestedScopeCapture.term) guard name
      (SourceScopeStack.requirement_formula_names guard (observe NestedScopeCapture.term) (NestedScopeCapture.zero "x")
        (by simp [guard, SourceGuards.requirements]) name member)
  · exact proved

/-- The fixture callback remains sound when each declared and ambient sort admits every integer. -/
theorem solver_domains (context : Guard Formula) :
    SourceEntailment.Sound integerModel (SolverDomain (fun _ _ => True) NestedScopeCapture.term context)
      NestedScopeCapture.solver := by
  intro declarations antecedent consequent
  have support := NestedScopeCapture.solver_sound declarations antecedent consequent
  cases answer : NestedScopeCapture.solver declarations antecedent consequent with
  | unknown => trivial
  | yes =>
      rw [answer] at support
      intro env _ assumed
      exact support env trivial assumed
  | no =>
      rw [answer] at support
      intro proved
      apply support
      intro env _ assumed
      exact proved env ⟨fun _ _ => trivial, fun _ _ => trivial⟩ assumed

/-- The complete full-guard judgment holds even though complete runtime evaluation returns Unknown. -/
theorem guard_logical : SourceQuotientGuards.Public integerModel (fun _ _ => True) NestedScopeCapture.term true guard :=
  SourceQuotientGuards.public_yes integerModel (by intro value; rfl) integer_laws (fun _ _ => True)
    NestedScopeCapture.solver NestedScopeCapture.term solver_domains true guard sparse_yes

end MicroCFTA.SourceQuotientExample
