import MicroCFTA.SameScopeIdentityCapture

/-!
# Guard against changing identity-entry precedence

A complete actual can turn the first sparse replacement of a formal into an
identity. The formula API removes identities before first-match lookup. The
new source check rejects an uncertain identity-shaped entry when a later
entry uses the same formal. It also retains the enclosing-renaming check.
-/
namespace MicroCFTA.SourceSubstitutionPrecedence
open SourceGuards SourceObservations SourceGuardRefinement
open Guards (Verdict)

/-- Reject an uncertain literal identity when a later entry can replace the same formal. -/
def ambiguousIdentityPrecedence : List (Resolved Formula) → Bool
  | [] => false
  | first :: rest =>
      (!first.identityKnown && decide (first.symbolReplacement.1 = first.symbolReplacement.2) &&
        rest.any (fun later => decide (later.symbolReplacement.1 = first.symbolReplacement.1))) ||
      ambiguousIdentityPrecedence rest

/-- The list scan excludes exactly the ordered pairs that can change identity precedence. -/
theorem precedence_false_iff (entries : List (Resolved Formula)) :
    ambiguousIdentityPrecedence entries = false ↔
      entries.Pairwise (fun first later => first.identityKnown = true ∨
        first.symbolReplacement.1 ≠ first.symbolReplacement.2 ∨
        later.symbolReplacement.1 ≠ first.symbolReplacement.1) := by
  induction entries with
  | nil => simp [ambiguousIdentityPrecedence]
  | cons first rest ih =>
      cases known : first.identityKnown <;>
        by_cases same : first.symbolReplacement.1 = first.symbolReplacement.2 <;>
        simp [ambiguousIdentityPrecedence, known, same, ih, List.pairwise_cons, List.any_eq_false]

/-- Complete actual identities leave the source behavior unchanged. -/
theorem known_precedence (entries : List (Resolved Formula))
    (known : entries.all Resolved.identityKnown = true) : ambiguousIdentityPrecedence entries = false := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      have head := (List.all_eq_true.mp known) first (by simp)
      have tail : rest.all Resolved.identityKnown = true := by
        apply List.all_eq_true.mpr
        intro entry member
        exact (List.all_eq_true.mp known) entry (by simp [member])
      simp [ambiguousIdentityPrecedence, head, ih tail]

/-- Unique formal names cannot expose a later replacement. -/
theorem distinct_formals (entries : List (Resolved Formula))
    (unique : (entries.map (fun entry => entry.symbolReplacement.1)).Nodup) :
    ambiguousIdentityPrecedence entries = false := by
  apply (precedence_false_iff entries).mpr
  have pairs : entries.Pairwise (fun first later => first.symbolReplacement.1 ≠ later.symbolReplacement.1) := by
    simpa only [List.Nodup, List.pairwise_map] using unique
  exact pairs.imp (fun different => Or.inr (Or.inr (Ne.symm different)))

/-- The repaired worker executes the existing syntax traversal with the new scope check. -/
def evaluateWith (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guard : Guard Formula) : Verdict :=
  SourceEnclosingRenames.evaluateWith formulas solver observed sameAt fresh unknown scopes positive guard
    ambiguousIdentityPrecedence

/-- A rejected identity-precedence scope returns Unknown before any nested query. -/
theorem blocked_scope (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool)
    (additions : List Substitution) (inner : Guard Formula) (resolved : List (Resolved Formula))
    (found : resolveMany formulas observed fresh unknown additions = some resolved)
    (blocked : ambiguousIdentityPrecedence resolved = true) :
    evaluateWith formulas solver observed sameAt fresh unknown scopes positive (.substitute additions inner) = .unknown := by
  simp [evaluateWith, SourceEnclosingRenames.evaluateWith, found, blocked]

/-- A known ambiguity table makes the added source check inactive through all syntax constructors. -/
theorem worker_known (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (scopes : List (List (Resolved Formula)))
    (positive : Bool) (guard : Guard Formula) :
    evaluateWith formulas solver observed sameAt fresh [] scopes positive guard =
      SourceEnclosingRenames.evaluateWith formulas solver observed sameAt fresh [] scopes positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [evaluateWith, SourceEnclosingRenames.evaluateWith] <;> rfl
  | substitute additions inner =>
      simp only [evaluateWith, SourceEnclosingRenames.evaluateWith]
      cases found : resolveMany formulas observed fresh [] additions with
      | none => rfl
      | some resolved =>
          have known := SourceKnownScopes.resolveMany_known formulas observed fresh additions resolved found
          have pass := known_precedence resolved known
          simp only [pass]
          split
          · rfl
          · exact worker_known formulas solver observed sameAt fresh (resolved :: scopes) positive inner
  | not inner =>
      simp only [evaluateWith, SourceEnclosingRenames.evaluateWith]
      exact worker_known formulas solver observed sameAt fresh scopes (!positive) inner
  | and parts | or parts =>
      simp only [evaluateWith, SourceEnclosingRenames.evaluateWith]
      congr 1
      apply List.map_congr_left
      intro part member
      exact worker_known formulas solver observed sameAt fresh scopes positive part
termination_by sizeOf guard

/-- The repaired private helper retains one identity table for a full nested scope. -/
def evaluateScoped [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula) : Verdict :=
  let table := substitutionValues formulas observed (sameAt []) guard
  evaluateWith formulas solver observed sameAt table.1 table.2 [] positive guard

/-- The repaired public dispatcher keeps independent Boolean allocation scopes. -/
def evaluate [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) : Guard Formula → Verdict
  | .and parts => combine positive (parts.map (evaluate formulas solver observed sameAt positive))
  | .or parts => combine (!positive) (parts.map (evaluate formulas solver observed sameAt positive))
  | .not inner => evaluate formulas solver observed sameAt (!positive) inner
  | .substitute [] inner => evaluate formulas solver observed sameAt positive inner
  | guard => evaluateScoped formulas solver observed sameAt positive guard

/-- The repaired sparse public entry. -/
def evaluateGuardWithShape [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (guard : Guard Formula) : Verdict :=
  evaluate formulas solver observed (sameShape formulas observed) true guard

/-- The repaired complete public entry. -/
def evaluateGuard [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (Label Formula)) : Verdict :=
  evaluate formulas solver (observe term) (sameTerm formulas term) true guard

/-- Unambiguous scoped calls have exactly the preceding evaluator result. -/
theorem scoped_known [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula)
    (known : ambiguous observed (sameAt []) guard = []) :
    evaluateScoped formulas solver observed sameAt positive guard =
      SourceEnclosingRenames.evaluateScoped formulas solver observed sameAt positive guard := by
  simp only [evaluateScoped, SourceEnclosingRenames.evaluateScoped, substitutionValues, known]
  exact worker_known formulas solver observed sameAt _ [] positive guard

/-- Unambiguous sparse calls preserve every verdict, including all Boolean branches. -/
theorem public_known [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (positive : Bool) (guard : Guard Formula)
    (known : ambiguous observed (sameAt []) guard = []) :
    evaluate formulas solver observed sameAt positive guard =
      SourceBooleanEntry.evaluate formulas solver observed sameAt positive guard := by
  have preceding : evaluate formulas solver observed sameAt positive guard =
      SourceEnclosingRenames.evaluate formulas solver observed sameAt positive guard := by
    cases guard with
    | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
        simpa only [evaluate, SourceEnclosingRenames.evaluate] using
          scoped_known formulas solver observed sameAt positive _ known
    | substitute additions inner =>
        cases additions with
        | nil =>
            simp only [evaluate, SourceEnclosingRenames.evaluate]
            have innerKnown := SourceBooleanBridge.unambiguous_subset _ _ _ inner (by simp [actualPaths]) known
            exact (public_known formulas solver observed sameAt positive inner innerKnown).trans
              (SourceEnclosingRenames.public_known formulas solver observed sameAt positive inner innerKnown).symm
        | cons first rest =>
            simpa only [evaluate, SourceEnclosingRenames.evaluate] using
              scoped_known formulas solver observed sameAt positive _ known
    | not inner =>
        simp only [evaluate, SourceEnclosingRenames.evaluate]
        have innerKnown := SourceBooleanBridge.unambiguous_subset _ _ _ inner (by simp [actualPaths]) known
        exact (public_known formulas solver observed sameAt (!positive) inner innerKnown).trans
          (SourceEnclosingRenames.public_known formulas solver observed sameAt (!positive) inner innerKnown).symm
    | and parts | or parts =>
        simp only [evaluate, SourceEnclosingRenames.evaluate]
        congr 1
        apply List.map_congr_left
        intro part member
        have innerKnown := SourceBooleanBridge.unambiguous_subset _ _ _ part (fun path present => by
          simpa only [actualPaths] using List.mem_flatMap.mpr ⟨part, member, present⟩) known
        exact (public_known formulas solver observed sameAt positive part innerKnown).trans
          (SourceEnclosingRenames.public_known formulas solver observed sameAt positive part innerKnown).symm
  exact preceding.trans (SourceEnclosingRenames.public_known formulas solver observed sameAt positive guard known)
termination_by sizeOf guard

/-- Complete evaluation is unchanged because every complete actual identity is known. -/
theorem complete_unchanged [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (Label Formula)) :
    evaluateGuard formulas solver guard term = SourceBooleanEntry.evaluateGuard formulas solver guard term :=
  public_known formulas solver (observe term) (sameTerm formulas term) true guard
    (ActualQuotient.complete_ambiguity_empty formulas term guard)

/-- The repaired sparse evaluator returns Unknown for the same-scope precedence witness. -/
theorem same_scope_unknown :
    evaluateGuardWithShape SourceFormula.operations NestedScopeCapture.solver
      (observe NestedScopeCapture.term) SameScopeIdentityCapture.guard = .unknown := by
  unfold evaluateGuardWithShape
  simp only [SameScopeIdentityCapture.guard, evaluate]
  unfold evaluateScoped
  change evaluateWith _ _ _ _
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameShape SourceFormula.operations (observe NestedScopeCapture.term) []) SameScopeIdentityCapture.guard).1
    (substitutionValues SourceFormula.operations (observe NestedScopeCapture.term)
      (sameShape SourceFormula.operations (observe NestedScopeCapture.term) []) SameScopeIdentityCapture.guard).2
    [] true SameScopeIdentityCapture.guard = .unknown
  rw [SameScopeIdentityCapture.tables.1]
  simp only [SameScopeIdentityCapture.guard, evaluateWith, SourceEnclosingRenames.evaluateWith]
  decide +kernel

/-- The original enclosing-capture witness still returns Unknown after the added check. -/
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
  simp only [NestedScopeCapture.guard, evaluateWith, SourceEnclosingRenames.evaluateWith]
  decide +kernel

/-- The repaired complete evaluator retains the counterexample's rejection. -/
theorem same_scope_complete_no :
    evaluateGuard SourceFormula.operations NestedScopeCapture.solver
      SameScopeIdentityCapture.guard NestedScopeCapture.term = .no := by
  rw [complete_unchanged]
  have rejected := SameScopeIdentityCapture.complete_no
  rw [SourceEnclosingRenames.complete_unchanged] at rejected
  exact rejected

end MicroCFTA.SourceSubstitutionPrecedence
