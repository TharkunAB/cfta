import MicroCFTA.SourceBooleanBridge
import MicroCFTA.NestedScopeCapture

/-!
# The enclosing-renaming safeguard at d6b8837

The source rejects one nested substitution when an unknown actual identity
uses an enclosing formal name. It does not reject every ambiguous guard.
The preceding evaluator remains available for historical counterexamples.
The default scope policy executes that upstream worker and dispatcher.
`SourceSubstitutionPrecedence` supplies the subsequent identity-precedence
check to the same syntax traversal.
-/
namespace MicroCFTA.SourceEnclosingRenames
open SourceGuards SourceObservations SourceGuardRefinement
open Guards (Verdict)

/-- Literal formal names from every enclosing substitution scope. -/
def enclosingFormals (scopes : List (List (Resolved Formula))) : List Name :=
  scopes.flatMap (fun scope => scope.map (fun resolved => resolved.symbolReplacement.1))

/-- Unknown actual identity and an enclosing formal name trigger the source safeguard. -/
def renamedByEnclosing (scopes : List (List (Resolved Formula))) (resolved : Resolved Formula) : Bool :=
  !resolved.identityKnown && (enclosingFormals scopes).contains resolved.symbolReplacement.2

/-- The source test uses the ambient literal name, not the allocated solver name. -/
theorem renamed_iff (scopes : List (List (Resolved Formula))) (resolved : Resolved Formula) :
    renamedByEnclosing scopes resolved = true ↔ resolved.identityKnown = false ∧
      ∃ scope ∈ scopes, ∃ outer ∈ scope, outer.symbolReplacement.1 = resolved.symbolReplacement.2 := by
  simp [renamedByEnclosing, enclosingFormals, List.mem_flatMap, List.mem_map]

/-- Complete identities do not trigger the safeguard. -/
theorem known_not_renamed (scopes : List (List (Resolved Formula))) (resolved : Resolved Formula)
    (known : resolved.identityKnown = true) : renamedByEnclosing scopes resolved = false := by
  simp [renamedByEnclosing, known]

/-- An outermost substitution has no enclosing formal names. -/
theorem outermost_not_renamed (resolved : Resolved Formula) : renamedByEnclosing [] resolved = false := by
  simp [renamedByEnclosing, enclosingFormals]

/-- The upstream scoped evaluator permits an additional source check at each scope entry. -/
def evaluateWith (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guard : Guard Formula)
    (unsafeScope : List (Resolved Formula) → Bool := fun _ => false) : Verdict :=
  match guard with
  | .top => polarize positive .yes
  | .bottom => polarize positive .no
  | .same left right =>
      match observed left, observed right with
      | some _, some _ => polarize positive (if left = right then .yes else
          match sameAt scopes left right with | some true => .yes | some false => .no | none => .unknown)
      | _, _ => absent positive
  | .entails left right =>
      match observed left, observed right with
      | some antecedent, some consequent => polarize positive
          (decideWith solver [] scopes
            (withActualAssumptions formulas scopes (applySubstitutions formulas scopes antecedent.refinement))
            (applySubstitutions formulas scopes consequent.refinement))
      | _, _ => absent positive
  | .satisfies target requirement =>
      match observed target with
      | some value => decideWith solver [] scopes
          (withActualAssumptions formulas scopes (applySubstitutions formulas scopes value.refinement))
          (applySubstitutions formulas scopes (if positive then requirement else formulas.negate requirement))
      | none => absent positive
  | .holds targets requirement =>
      match observeMany observed targets with
      | some values =>
          let prepared := contract formulas targets values
          decideWith solver (prepared.1.map (fun name => (name, valueName))) scopes
            (withActualAssumptions formulas scopes (applySubstitutions formulas scopes prepared.2))
            (applySubstitutions formulas scopes (if positive then requirement else formulas.negate requirement))
      | none => absent positive
  | .substitute additions inner =>
      match resolveMany formulas observed fresh unknown additions with
      | some resolved =>
          if resolved.any (renamedByEnclosing scopes) || unsafeScope resolved then .unknown
          else evaluateWith formulas solver observed sameAt fresh unknown (resolved :: scopes) positive inner unsafeScope
      | none => absent positive
  | .not inner => evaluateWith formulas solver observed sameAt fresh unknown scopes (!positive) inner unsafeScope
  | .and parts => combine positive (parts.map (fun part => evaluateWith formulas solver observed sameAt fresh unknown scopes positive part unsafeScope))
  | .or parts => combine (!positive) (parts.map (fun part => evaluateWith formulas solver observed sameAt fresh unknown scopes positive part unsafeScope))


termination_by sizeOf guard

/-- A blocked scope returns Unknown for either polarity before the nested query. -/
theorem blocked_scope (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool)
    (additions : List Substitution) (inner : Guard Formula) (resolved : List (Resolved Formula))
    (found : resolveMany formulas observed fresh unknown additions = some resolved)
    (blocked : resolved.any (renamedByEnclosing scopes) = true) :
    evaluateWith formulas solver observed sameAt fresh unknown scopes positive (.substitute additions inner) = .unknown := by
  simp [evaluateWith, found, blocked]

/-- The new scope test can discard a verdict but cannot introduce a different decided verdict. -/
theorem worker_refines (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guard : Guard Formula) :
    Refines (evaluateWith formulas solver observed sameAt fresh unknown scopes positive guard)
      (SourceGuards.evaluateWith formulas solver observed sameAt fresh unknown scopes positive guard) := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [evaluateWith, SourceGuards.evaluateWith]
      exact refines_refl _
  | substitute additions inner =>
      simp only [evaluateWith, SourceGuards.evaluateWith]
      cases found : resolveMany formulas observed fresh unknown additions with
      | none => exact refines_refl _
      | some resolved =>
          dsimp only
          split
          · exact Or.inl rfl
          · exact worker_refines formulas solver observed sameAt fresh unknown (resolved :: scopes) positive inner
  | not inner =>
      simp only [evaluateWith, SourceGuards.evaluateWith]
      exact worker_refines formulas solver observed sameAt fresh unknown scopes (!positive) inner
  | and parts | or parts =>
      simp only [evaluateWith, SourceGuards.evaluateWith]
      apply combine_map_refines
      intro part member
      exact worker_refines formulas solver observed sameAt fresh unknown scopes positive part
termination_by sizeOf guard

/-- An empty ambiguity table makes every resolved scope pass the new test. -/
theorem worker_known (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (scopes : List (List (Resolved Formula)))
    (positive : Bool) (guard : Guard Formula) :
    evaluateWith formulas solver observed sameAt fresh [] scopes positive guard =
      SourceGuards.evaluateWith formulas solver observed sameAt fresh [] scopes positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [evaluateWith, SourceGuards.evaluateWith] <;> rfl
  | substitute additions inner =>
      simp only [evaluateWith, SourceGuards.evaluateWith]
      cases found : resolveMany formulas observed fresh [] additions with
      | none => rfl
      | some resolved =>
          have known := SourceKnownScopes.resolveMany_known formulas observed fresh additions resolved found
          have pass : resolved.any (renamedByEnclosing scopes) = false := by
            apply List.any_eq_false.mpr
            intro entry member
            simp [known_not_renamed scopes entry ((List.all_eq_true.mp known) entry member)]
          simp only [pass]
          exact worker_known formulas solver observed sameAt fresh (resolved :: scopes) positive inner
  | not inner =>
      simp only [evaluateWith, SourceGuards.evaluateWith]
      exact worker_known formulas solver observed sameAt fresh scopes (!positive) inner
  | and parts | or parts =>
      simp only [evaluateWith, SourceGuards.evaluateWith]
      congr 1
      apply List.map_congr_left
      intro part member
      exact worker_known formulas solver observed sameAt fresh scopes positive part
termination_by sizeOf guard

/-- The upstream private helper retains one identity table for the complete scope. -/
def evaluateScoped [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) : Verdict :=
  let table := substitutionValues formulas observed (sameAt []) guard
  evaluateWith formulas solver observed sameAt table.1 table.2 [] positive guard

/-- Public Boolean operands allocate independent tables, as in the source dispatcher. -/
def evaluate [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) : Guard Formula → Verdict
  | .and parts => combine positive (parts.map (evaluate formulas solver observed sameAt positive))
  | .or parts => combine (!positive) (parts.map (evaluate formulas solver observed sameAt positive))
  | .not inner => evaluate formulas solver observed sameAt (!positive) inner
  | .substitute [] inner => evaluate formulas solver observed sameAt positive inner
  | guard => evaluateScoped formulas solver observed sameAt positive guard

/-- The upstream sparse public entry before the same-scope repair. -/
def evaluateGuardWithShape [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (guard : Guard Formula) : Verdict :=
  evaluate formulas solver observed (sameShape formulas observed) true guard

/-- The upstream complete public entry. -/
def evaluateGuard [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (Label Formula)) : Verdict :=
  evaluate formulas solver (observe term) (sameTerm formulas term) true guard

/-- Unambiguous scoped calls retain the previous exact evaluator result. -/
theorem scoped_known [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula)
    (known : ambiguous observed (sameAt []) guard = []) :
    evaluateScoped formulas solver observed sameAt positive guard =
      SourceBooleanEntry.evaluateScoped formulas solver observed sameAt positive guard := by
  rw [SourceBooleanEntry.scoped_eq]
  simp only [evaluateScoped, substitutionValues, known]
  exact worker_known formulas solver observed sameAt _ [] positive guard

/-- Every public Boolean branch retains the previous result when the outer actual table is unambiguous. -/
theorem public_known [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula)
    (known : ambiguous observed (sameAt []) guard = []) :
    evaluate formulas solver observed sameAt positive guard =
      SourceBooleanEntry.evaluate formulas solver observed sameAt positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simpa only [evaluate, SourceBooleanEntry.evaluate] using
        scoped_known formulas solver observed sameAt positive _ known
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [evaluate, SourceBooleanEntry.evaluate]
          exact public_known formulas solver observed sameAt positive inner
            (SourceBooleanBridge.unambiguous_subset _ _ _ inner (by simp [actualPaths]) known)
      | cons first rest =>
          simpa only [evaluate, SourceBooleanEntry.evaluate] using
            scoped_known formulas solver observed sameAt positive _ known
  | not inner =>
      simp only [evaluate, SourceBooleanEntry.evaluate]
      exact public_known formulas solver observed sameAt (!positive) inner
        (SourceBooleanBridge.unambiguous_subset _ _ _ inner (by simp [actualPaths]) known)
  | and parts | or parts =>
      simp only [evaluate, SourceBooleanEntry.evaluate]
      congr 1
      apply List.map_congr_left
      intro part member
      exact public_known formulas solver observed sameAt positive part
        (SourceBooleanBridge.unambiguous_subset _ _ _ part (fun path present => by
          simpa only [actualPaths] using List.mem_flatMap.mpr ⟨part, member, present⟩) known)
termination_by sizeOf guard

/-- Complete term evaluation is unchanged, since complete identities are always known. -/
theorem complete_unchanged [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (Label Formula)) :
    evaluateGuard formulas solver guard term = SourceBooleanEntry.evaluateGuard formulas solver guard term :=
  public_known formulas solver (observe term) (sameTerm formulas term) true guard
    (ActualQuotient.complete_ambiguity_empty formulas term guard)

/-- The repaired public sparse evaluator rejects the retained nested-capture witness. -/
theorem nested_capture_unknown :
    evaluateGuardWithShape SourceFormula.operations NestedScopeCapture.solver
      (observe NestedScopeCapture.term) NestedScopeCapture.guard = .unknown := by
  unfold evaluateGuardWithShape
  simp only [NestedScopeCapture.guard, evaluate]
  unfold evaluateScoped
  change evaluateWith _ _ _ _
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameShape SourceFormula.operations (observe NestedScopeCapture.term) []) NestedScopeCapture.guard).1
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameShape SourceFormula.operations (observe NestedScopeCapture.term) []) NestedScopeCapture.guard).2
    [] true NestedScopeCapture.guard = .unknown
  rw [NestedScopeCapture.tables.1]
  simp only [NestedScopeCapture.guard, evaluateWith]
  decide +kernel

/-- Unknown identity alone does not reject an outermost substitution, even when its table is ambiguous. -/
theorem ambiguous_outer_scope (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (additions : List Substitution) (resolved : List (Resolved Formula))
    (found : resolveMany formulas observed fresh unknown additions = some resolved) :
    evaluateWith formulas solver observed sameAt fresh unknown [] true (.substitute additions .top) = .yes := by
  have pass : resolved.any (renamedByEnclosing []) = false := by
    apply List.any_eq_false.mpr
    intro entry member
    simp [outermost_not_renamed]
  simp [evaluateWith, found, pass, polarize]

end MicroCFTA.SourceEnclosingRenames
