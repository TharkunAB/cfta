import MicroCFTA.SourceScopeStack
import MicroCFTA.SourceEntailment

/-!
# Source query formulas under paired scope environments

Theorems below derive the actual-assumption and scoped-body correspondence
from exact source resolution calls. Per-environment name agreement remains
explicit, so callers can use both forward and reverse constructed maps.
-/
namespace MicroCFTA.SourceScopeQueries
open FullSyntax FormulaSubstitution SourceFormula SourceScopeStack

private theorem resolved_unique (guard : SourceGuards.Guard Formula) (observed : SourceGuards.Observations Formula)
    (recipes : List Recipe) (first second : List Scope)
    (left : Resolves guard observed recipes first) (right : Resolves guard observed recipes second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
      cases right with
      | cons otherHead otherTail =>
          have same := Option.some.inj (head.1.symm.trans otherHead.1)
          simp only [same, ih _ otherTail]

private theorem resolve_cons (guard : SourceGuards.Guard Formula) (observed : SourceGuards.Observations Formula)
    (entry : SourceGuards.Substitution) (rest : Recipe) :
    resolve guard observed (entry :: rest) = (do
      let first ← SourceGuards.resolve operations observed
        (SourceGuards.substitutionValues operations observed (SourceObservations.sameShape operations observed []) guard).1
        (SourceGuards.substitutionValues operations observed (SourceObservations.sameShape operations observed []) guard).2 entry
      let others ← resolve guard observed rest
      pure (first :: others)) := by simp only [resolve, SourceGuards.resolveMany]

/-- Source-resolved stacks preserve every scoped ambient formula under related environments. -/
theorem formula_related (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv)
    (formula : Formula) (names : ∀ name ∈ formulaNames formula, name ∈ SourceSemanticNames.ambient operations first guard) :
    Holds model firstEnv (SourceGuards.applySubstitutions operations scopes formula) ↔
      Holds model secondEnv (SourceGuards.applySubstitutions operations other formula) := by
  obtain ⟨computed, computedResolved, aligned⟩ := transport guard first second reads recipes scopes resolved
  have unique := resolved_unique guard second recipes computed other computedResolved otherResolved
  subst computed
  apply SourceScopeEnvironment.scoped_formula_equivalent model nullary _ _
    (SourceSemanticNames.live_injective operations guard first second reads) firstEnv secondEnv related
    scopes other aligned (closed guard first second recipes scopes resolved) formula
  intro name member
  have ambient := names name member
  exact ⟨List.mem_append_left _ ambient, SourceSemanticNames.ambient_fixed operations guard first second name ambient⟩

/-- One actual source assumption agrees under the same finite environment relation. -/
theorem actual_related (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (entry : SourceGuards.Substitution)
    (positions : entry.actual ∈ SourceGuards.sensitive guard ∧ entry.formal ∈ SourceGuards.sensitive guard)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv)
    (old new : SourceGuards.Resolved Formula)
    (oldFound : SourceGuards.resolve operations first
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).1
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations second
      (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).1
      (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).2 entry = some new) :
    Holds model firstEnv old.actualAssumption ↔ Holds model secondEnv new.actualAssumption := by
  obtain ⟨actual, _, atActual, _⟩ := SourceActuals.resolve_exists operations first _ _ entry old oldFound
  have closed := SourceSemanticNames.resolve_live operations guard first second entry old positions.1 positions.2 oldFound
  obtain ⟨computed, result, meaning⟩ := SourceActualAssumptions.resolve_tables_assumption model nullary firstEnv secondEnv
    guard first second reads entry actual old positions.1 positions.2 atActual oldFound
    (by
      intro name member
      have ambient := observed_formula_names guard first entry.actual actual
        (SourceReadAgreement.sensitive_requested guard entry.actual positions.1) atActual name member
      have exact := related name (List.mem_append_left _ ambient)
      simpa only [SourceSemanticNames.ambient_fixed operations guard first second name ambient] using exact)
    (related old.replacement.2 closed.2.1)
  have same : computed = new := Option.some.inj (result.symm.trans newFound)
  exact same ▸ meaning

/-- Every ordered actual assumption in one successful scope has the paired full formula meaning. -/
theorem scope_actuals_related (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipe : Recipe) (requested : Requested guard recipe)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv)
    (scope other : Scope) (oldFound : resolve guard first recipe = some scope) (newFound : resolve guard second recipe = some other) :
    Language.All₂ (fun old new => Holds model firstEnv old.actualAssumption ↔ Holds model secondEnv new.actualAssumption) scope other := by
  induction recipe generalizing scope other with
  | nil => simp [resolve, SourceGuards.resolveMany] at oldFound newFound; subst scope; subst other; exact .nil
  | cons entry rest ih =>
      cases a : SourceGuards.resolve operations first
          (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).1
          (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).2 entry with
      | none => simp [resolve_cons, a] at oldFound
      | some old =>
          cases b : resolve guard first rest with
          | none => simp [resolve_cons, a, b] at oldFound
          | some oldRest =>
              have oldSame : old :: oldRest = scope := by simpa [resolve_cons, a, b] using oldFound
              cases c : SourceGuards.resolve operations second
                  (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).1
                  (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).2 entry with
              | none => simp [resolve_cons, c] at newFound
              | some new =>
                  cases d : resolve guard second rest with
                  | none => simp [resolve_cons, c, d] at newFound
                  | some newRest =>
                      have newSame : new :: newRest = other := by simpa [resolve_cons, c, d] using newFound
                      subst scope; subst other
                      exact .cons (actual_related model nullary guard first second reads entry (requested entry (by simp))
                        firstEnv secondEnv related old new a c)
                        (ih (fun value member => requested value (by simp [member])) oldRest newRest b d)

private theorem all₂_forall {Left Right : Type} (left : List Left) (right : List Right)
    (first : Left → Prop) (second : Right → Prop)
    (paired : Language.All₂ (fun a b => first a ↔ second b) left right) :
    (∀ a ∈ left, first a) ↔ ∀ b ∈ right, second b := by
  induction paired with
  | nil => simp
  | cons head tail ih => simpa only [List.forall_mem_cons] using and_congr head ih

/-- The full ordered stack retains all ambient actual assumptions. -/
theorem stack_actuals_related (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv) :
    (∀ scope ∈ scopes, ∀ entry ∈ scope, Holds model firstEnv entry.actualAssumption) ↔
      ∀ scope ∈ other, ∀ entry ∈ scope, Holds model secondEnv entry.actualAssumption := by
  apply all₂_forall
  induction resolved generalizing other with
  | nil => cases otherResolved; exact .nil
  | @cons recipe scope recipes scopes head tail ih =>
      cases otherResolved with
      | cons otherHead otherTail =>
          exact .cons
            (all₂_forall _ _ _ _ (scope_actuals_related model nullary guard first second reads recipe head.2
              firstEnv secondEnv related _ _ head.1 otherHead.1))
            (ih _ otherTail)

/-- The source query antecedent combines the scope fold and ambient actual assumptions exactly. -/
theorem antecedent_related (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv)
    (formula : Formula) (names : ∀ name ∈ formulaNames formula, name ∈ SourceSemanticNames.ambient operations first guard) :
    Holds model firstEnv (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes formula)) ↔
      Holds model secondEnv (SourceGuards.withActualAssumptions operations other (SourceGuards.applySubstitutions operations other formula)) := by
  rw [actual_assumptions_semantics model laws, actual_assumptions_semantics model laws]
  exact and_congr (stack_actuals_related model nullary guard first second reads recipes scopes other resolved otherResolved
    firstEnv secondEnv related)
    (formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
      firstEnv secondEnv related formula names)

/-- Every target environment has a corresponding source environment through the actual fresh-name table. -/
theorem forward_related (model : Interpretation Value)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula) (env : Name → Value) :
    SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard)
      (renamedEnvironment model env (SourceFreshTables.tableRenaming operations guard first second)) env := by
  intro name _
  exact FreshEnvironment.environment_names model env _ (SourceFreshTables.renaming_unique operations guard first second).1 name

/-- Source-resolved nested queries preserve mathematical entailment across conflicting fresh names.
The environment domain is unrestricted here. Sorted declaration domains are a separate backend contract. -/
theorem query_entails_iff (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceSemanticNames.ambient operations first guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard) :
    SourceEntailment.Entails model (fun _ => True)
      (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
      (SourceGuards.applySubstitutions operations scopes consequent) ↔
    SourceEntailment.Entails model (fun _ => True)
      (SourceGuards.withActualAssumptions operations other (SourceGuards.applySubstitutions operations other antecedent))
      (SourceGuards.applySubstitutions operations other consequent) := by
  constructor
  · intro proved env _ assumed
    have related := forward_related model guard first second env
    exact (formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
      _ env related consequent rightNames).mp
      (proved _ True.intro ((antecedent_related model nullary laws guard first second reads recipes scopes other
        resolved otherResolved _ env related antecedent leftNames).mpr assumed))
  · intro proved env _ assumed
    have unique := SourceFreshTables.renaming_unique operations guard first second
    have related := SourceScopeEnvironment.lift_related model _ _ unique.1 unique.2
      (SourceSemanticNames.live_avoid operations guard first second reads) env
    exact (formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
      env _ related consequent rightNames).mpr
      (proved _ True.intro ((antecedent_related model nullary laws guard first second reads recipes scopes other
        resolved otherResolved env _ related antecedent leftNames).mp assumed))

end MicroCFTA.SourceScopeQueries
