import MicroCFTA.SourceIdentityQuotient

/-!
# Forward source queries through complete actual identification

The environment relation is derived from the executed identity map and the
accepted source scope stack. Complete declaration removal is handled by the
ambient sort domain. No reverse map or exact solver verdict is assumed.
-/
namespace MicroCFTA.SourceQuotientQueries
open FullSyntax SourceFormula FormulaSubstitution
open SourceGuards (Path Guard Substitution Resolved)
open SourceObservations SourceQuotientEnvironment SourceIdentityQuotient
abbrev Recipe := List Substitution

/-- A scope recipe reads actual positions and formal positions from its enclosing guard. -/
def Requested (guard : Guard Formula) (recipe : Recipe) : Prop :=
  ∀ entry ∈ recipe, entry.actual ∈ SourceGuards.actualPaths guard ∧ entry.formal ∈ SourceGuards.paths guard

/-- The exact scope traversal with the supplied sparse or complete initial identity comparison. -/
def resolve (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (recipe : Recipe) : Option Scope :=
  let table := SourceGuards.substitutionValues operations (observe term) sameAt guard
  SourceGuards.resolveMany operations (observe term) table.1 table.2 recipe

/-- Each recorded source scope is an actual successful resolution at requested positions. -/
def Resolves (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (recipes : List Recipe) (scopes : List Scope) : Prop :=
  Language.All₂ (fun recipe scope => resolve term guard sameAt recipe = some scope ∧ Requested guard recipe) recipes scopes

/-- Changing identity tables cannot remove an actual or formal path that already resolved. -/
theorem resolve_exists (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (first second : Path → Path → Option Bool) (recipe : Recipe) (old : Scope)
    (found : resolve term guard first recipe = some old) :
    ∃ new, resolve term guard second recipe = some new := by
  induction recipe generalizing old with
  | nil => exact ⟨[], rfl⟩
  | cons entry rest ih =>
      cases head : SourceGuards.resolve operations (observe term)
          (SourceGuards.substitutionValues operations (observe term) first guard).1
          (SourceGuards.substitutionValues operations (observe term) first guard).2 entry with
      | none => simp [resolve, SourceGuards.resolveMany, head] at found
      | some row =>
          cases tail : resolve term guard first rest with
          | none => simp only [resolve] at tail; simp [resolve, SourceGuards.resolveMany, head, tail] at found
          | some rows =>
              obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry row head
              have otherHead : ∃ new, SourceGuards.resolve operations (observe term)
                  (SourceGuards.substitutionValues operations (observe term) second guard).1
                  (SourceGuards.substitutionValues operations (observe term) second guard).2 entry = some new := by
                simp [SourceGuards.resolve, atActual, atFormal]
              obtain ⟨newRow, newHead⟩ := otherHead
              obtain ⟨newRows, newTail⟩ := ih rows tail
              refine ⟨newRow :: newRows, ?_⟩
              simp only [resolve] at newTail
              simp [resolve, SourceGuards.resolveMany, newHead, newTail]

/-- Complete resolution exists for every source stack that resolved sparsely. -/
theorem complete_exists (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (recipes : List Recipe) (old : List Scope)
    (found : Resolves term guard (sameShape operations (observe term) []) recipes old) :
    ∃ new, Resolves term guard (sameTerm operations term []) recipes new := by
  induction found with
  | nil => exact ⟨[], .nil⟩
  | @cons recipe scope recipes scopes head tail ih =>
      obtain ⟨newScope, resolved⟩ := resolve_exists term guard _ (sameTerm operations term []) recipe scope head.1
      obtain ⟨newScopes, remaining⟩ := ih
      exact ⟨newScope :: newScopes, .cons ⟨resolved, head.2⟩ remaining⟩

/-- Ordered source traversals retain every relation proved for their corresponding entries. -/
theorem resolve_relation (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (first second : Path → Path → Option Bool) (recipe : Recipe)
    (relation : Resolved Formula → Resolved Formula → Prop)
    (each : ∀ entry ∈ recipe, ∀ old new,
      SourceGuards.resolve operations (observe term) (SourceGuards.substitutionValues operations (observe term) first guard).1
        (SourceGuards.substitutionValues operations (observe term) first guard).2 entry = some old →
      SourceGuards.resolve operations (observe term) (SourceGuards.substitutionValues operations (observe term) second guard).1
        (SourceGuards.substitutionValues operations (observe term) second guard).2 entry = some new → relation old new)
    (old new : Scope) (oldFound : resolve term guard first recipe = some old)
    (newFound : resolve term guard second recipe = some new) : Language.All₂ relation old new := by
  induction recipe generalizing old new with
  | nil => simp [resolve, SourceGuards.resolveMany] at oldFound newFound; subst old; subst new; exact .nil
  | cons entry rest ih =>
      cases a : SourceGuards.resolve operations (observe term)
          (SourceGuards.substitutionValues operations (observe term) first guard).1
          (SourceGuards.substitutionValues operations (observe term) first guard).2 entry <;>
        cases b : SourceGuards.resolve operations (observe term)
          (SourceGuards.substitutionValues operations (observe term) second guard).1
          (SourceGuards.substitutionValues operations (observe term) second guard).2 entry <;>
        cases c : resolve term guard first rest <;>
        cases d : resolve term guard second rest <;>
        simp only [resolve] at c d <;>
        simp [resolve, SourceGuards.resolveMany, a, b, c, d] at oldFound newFound
      subst old; subst new
      exact .cons (each entry (by simp) _ _ a b)
        (ih (fun value member => each value (by simp [member])) _ _ c d)

/-- Two successful source stacks lift any local record relation in source order. -/
theorem stack_relation (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (first second : Path → Path → Option Bool) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard first recipes old) (newFound : Resolves term guard second recipes new)
    (relation : Resolved Formula → Resolved Formula → Prop)
    (each : ∀ recipe, Requested guard recipe → ∀ entry ∈ recipe, ∀ a b,
      SourceGuards.resolve operations (observe term) (SourceGuards.substitutionValues operations (observe term) first guard).1
        (SourceGuards.substitutionValues operations (observe term) first guard).2 entry = some a →
      SourceGuards.resolve operations (observe term) (SourceGuards.substitutionValues operations (observe term) second guard).1
        (SourceGuards.substitutionValues operations (observe term) second guard).2 entry = some b → relation a b) :
    Language.All₂ (Language.All₂ relation) old new := by
  induction oldFound generalizing new with
  | nil => cases newFound; exact .nil
  | @cons recipe scope recipes scopes head tail ih =>
      cases newFound with
      | cons otherHead otherTail =>
          exact .cons (resolve_relation term guard first second recipe relation (each recipe head.2) _ _ head.1 otherHead.1)
            (ih _ otherTail)

/-- The actual sparse and complete source stacks satisfy the derived forward environment conditions. -/
theorem stack_pair (model : Interpretation Value) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (env : Name → Value) :
    Language.All₂ (Language.All₂ (Pair (SourceGuards.usedNames operations (observe term) guard))) old new ∧
    Language.All₂ (Language.All₂ (fun a b =>
      renamedEnvironment model env (SourceIdentityMap.names operations term guard) a.replacement.2 = env b.replacement.2)) old new := by
  constructor
  · apply stack_relation term guard _ _ recipes old new oldFound newFound
    intro recipe requested entry member a b first second
    exact resolve_pair term guard entry (requested entry member).1 (requested entry member).2 a b first second
  · apply stack_relation term guard _ _ recipes old new oldFound newFound
    intro recipe requested entry member a b first second
    exact resolve_values model term guard entry (requested entry member).1 a b first second env

/-- All current formula constructors preserve meaning under the derived accepted-scope quotient. -/
theorem formula_forward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (formula : Formula)
    (names : ∀ name ∈ formulaNames formula, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (env : Name → Value) :
    Holds model (renamedEnvironment model env (SourceIdentityMap.names operations term guard))
      (SourceGuards.applySubstitutions operations old formula) ↔
      Holds model env (SourceGuards.applySubstitutions operations new formula) := by
  have paired := stack_pair model term guard recipes old new oldFound newFound env
  exact scoped_formula model nullary _ _ env old new paired.1 accepted (ambient_values model term guard env)
    paired.2 formula names

/-- Every source actual assumption is transported by the actual value correspondence. -/
theorem actual_forward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (entry : Substitution)
    (requested : entry.actual ∈ SourceGuards.actualPaths guard) (old new : Resolved Formula)
    (oldFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).2 entry = some new)
    (env : Name → Value) :
    Holds model (renamedEnvironment model env (SourceIdentityMap.names operations term guard)) old.actualAssumption ↔
      Holds model env new.actualAssumption := by
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry old oldFound
  rw [resolved_row term guard _ entry actual formal requested atActual atFormal old oldFound,
    resolved_row term guard _ entry actual formal requested atActual atFormal new newFound]
  apply SourceActualAssumptions.assumption_equivalent model nullary
  · intro name member
    apply ambient_values model term guard env
    exact SourceSemanticNames.free_used operations (observe term) guard entry.actual actual name
      (SourceReadAgreement.sensitive_requested guard _ (SourceIdentityReads.actual_sensitive guard _ requested)) atActual
      (by simpa [operations, FullSyntax.freeNames] using member)
  · exact SourceIdentityMap.environment_actual model operations term guard env _
      (actual_member (observe term) guard entry.actual actual requested atActual)

/-- Universal requirements on related list entries are equivalent. -/
theorem all_related {α β : Type} {left : List α} {right : List β} (first : α → Prop) (second : β → Prop)
    (paired : Language.All₂ (fun a b => first a ↔ second b) left right) :
    (∀ a ∈ left, first a) ↔ ∀ b ∈ right, second b := by
  induction paired with
  | nil => simp
  | cons head tail ih => simpa only [List.forall_mem_cons] using and_congr head ih

/-- Ambient actual assumptions are preserved even when complete declarations are dropped. -/
theorem assumptions_forward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (env : Name → Value) :
    (∀ scope ∈ old, ∀ entry ∈ scope,
      Holds model (renamedEnvironment model env (SourceIdentityMap.names operations term guard)) entry.actualAssumption) ↔
    (∀ scope ∈ new, ∀ entry ∈ scope, Holds model env entry.actualAssumption) := by
  apply all_related
  have paired := stack_relation term guard _ _ recipes old new oldFound newFound
    (fun a b => Holds model (renamedEnvironment model env (SourceIdentityMap.names operations term guard)) a.actualAssumption ↔
      Holds model env b.actualAssumption) (by
      intro recipe requested entry member a b first second
      exact actual_forward model nullary term guard entry (requested entry member).1 a b first second env)
  exact paired.imp (fun _ _ scope => all_related _ _ scope)

/-- The complete source antecedent combines transported actual assumptions and transported scoped formulas. -/
theorem antecedent_forward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (formula : Formula)
    (names : ∀ name ∈ formulaNames formula, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (env : Name → Value) :
    Holds model (renamedEnvironment model env (SourceIdentityMap.names operations term guard))
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old formula)) ↔
    Holds model env (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new formula)) := by
  rw [actual_assumptions_semantics model laws, actual_assumptions_semantics model laws]
  exact and_congr (assumptions_forward model nullary term guard recipes old new oldFound newFound env)
    (formula_forward model nullary term guard recipes old new oldFound newFound accepted formula names env)

/-- Original source names retain their externally supplied sort domains. -/
def AmbientDomain (sortDomain : Name → Value → Prop) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (env : Name → Value) : Prop :=
  ∀ name ∈ SourceGuards.usedNames operations (observe term) guard, sortDomain name (env name)

/-- A query admits the ambient domains and all generated declaration domains. -/
def Domain (sortDomain : Name → Value → Prop) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (scopes : List Scope) (env : Name → Value) : Prop :=
  AmbientDomain sortDomain term guard env ∧ SourceSortedQueries.Domain sortDomain scopes env

/-- A removed declaration receives its original ambient domain; a retained declaration receives its complete domain. -/
theorem row_domain_forward (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (entry : Substitution)
    (requested : entry.actual ∈ SourceGuards.actualPaths guard) (old new : Resolved Formula)
    (oldFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).2 entry = some new)
    (env : Name → Value) (ambient : AmbientDomain sortDomain term guard env)
    (declared : ∀ binding, new.declaration = some binding → sortDomain binding.2 (env binding.1)) :
    ∀ binding, old.declaration = some binding → sortDomain binding.2
      (renamedEnvironment model env (SourceIdentityMap.names operations term guard) binding.1) := by
  intro binding found
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry old oldFound
  have oldFields := resolved_declaration term guard _ entry actual formal requested atActual atFormal old oldFound binding found
  rw [oldFields.1, oldFields.2, resolve_values model term guard entry requested old new oldFound newFound env]
  cases present : new.declaration with
  | none =>
      rw [resolved_undeclared term guard _ entry actual formal requested atActual atFormal new newFound present]
      exact ambient actual.name (SourceLogicalNames.actual_name_used operations (observe term) guard _
        (actual_member (observe term) guard entry.actual actual requested atActual))
  | some other =>
      have newFields := resolved_declaration term guard _ entry actual formal requested atActual atFormal new newFound other present
      simpa only [newFields.1, newFields.2] using declared other present

/-- All collected and deduplicated declaration domains pull back through the actual identity quotient. -/
theorem domain_forward (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (env : Name → Value)
    (allowed : Domain sortDomain term guard new env) :
    Domain sortDomain term guard old (renamedEnvironment model env (SourceIdentityMap.names operations term guard)) := by
  constructor
  · intro name member
    rw [ambient_values model term guard env name member]
    exact allowed.1 name member
  · apply (SourceSortedQueries.domain_iff sortDomain old _).mpr
    have paired := stack_relation term guard _ _ recipes old new oldFound newFound
      (fun a b => (∀ binding, b.declaration = some binding → sortDomain binding.2 (env binding.1)) →
        ∀ binding, a.declaration = some binding → sortDomain binding.2
          (renamedEnvironment model env (SourceIdentityMap.names operations term guard) binding.1)) (by
          intro recipe requested entry member a b first second
          exact row_domain_forward model sortDomain term guard entry (requested entry member).1 a b first second env allowed.1)
    intro scope member entry present
    obtain ⟨other, otherMember, related⟩ := member_left paired scope member
    obtain ⟨newEntry, newMember, row⟩ := member_left related entry present
    exact row ((SourceSortedQueries.domain_iff sortDomain new env).mp allowed.2 other otherMember newEntry newMember)

/-- Positive entailment survives the executed non-injective query transport, including dropped declarations. -/
theorem entails_yes (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (proved : SourceEntailment.Entails model (Domain sortDomain term guard old)
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent)) :
    SourceEntailment.Entails model (Domain sortDomain term guard new)
      (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new antecedent))
      (SourceGuards.applySubstitutions operations new consequent) := by
  have identified := SourceEntailment.rename_yes model nullary
    (Domain sortDomain term guard old) (Domain sortDomain term guard new)
    (SourceIdentityMap.names operations term guard) _ _
    (domain_forward model sortDomain term guard recipes old new oldFound newFound) proved
  intro env allowed assumed
  apply (formula_forward model nullary term guard recipes old new oldFound newFound accepted consequent rightNames env).mp
  apply (substitute_semantics model nullary env _ _).mp
  apply identified env allowed
  apply (substitute_semantics model nullary env _ _).mpr
  exact (antecedent_forward model nullary laws term guard recipes old new oldFound newFound accepted antecedent leftNames env).mpr assumed

/-- Without sort restrictions, the existing identification theorem composes with the exact source query construction. -/
theorem entails_yes_unrestricted (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (proved : SourceEntailment.Entails model (fun _ => True)
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent)) :
    SourceEntailment.Entails model (fun _ => True)
      (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new antecedent))
      (SourceGuards.applySubstitutions operations new consequent) := by
  have identified := SourceEntailment.identify_yes model nullary (SourceIdentityMap.names operations term guard) _ _ proved
  intro env allowed assumed
  apply (formula_forward model nullary term guard recipes old new oldFound newFound accepted consequent rightNames env).mp
  apply (substitute_semantics model nullary env _ _).mp
  apply identified env allowed
  apply (substitute_semantics model nullary env _ _).mpr
  exact (antecedent_forward model nullary laws term guard recipes old new oldFound newFound accepted antecedent leftNames env).mpr assumed

/-- Each successful current scope-entry test extends the exact accepted-stack invariant. -/
theorem accepted_cons (scope : Scope) (outer : List Scope) (accepted : Accepted outer)
    (passed : (scope.any (SourceEnclosingRenames.renamedByEnclosing outer) ||
      SourceSubstitutionPrecedence.ambiguousIdentityPrecedence scope) = false) : Accepted (scope :: outer) := by
  have both := Bool.or_eq_false_iff.mp passed
  exact ⟨both.2, both.1, accepted⟩

/-- The declared solver domain includes its ambient context and its explicit fresh declarations. -/
def SolverDomain (sortDomain : Name → Value → Prop) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (declarations : List (Name × Name)) (env : Name → Value) : Prop :=
  AmbientDomain sortDomain term guard env ∧ ∀ binding ∈ declarations, sortDomain binding.2 (env binding.1)

/-- A sound sparse Yes yields logical entailment for the complete current query, including ambiguous actuals. -/
theorem solver_yes_logical (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (solver : SourceGuards.Entailment Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (yes : SourceGuards.decideWith solver [] old
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent) = .yes) :
    SourceEntailment.Entails model (Domain sortDomain term guard new)
      (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new antecedent))
      (SourceGuards.applySubstitutions operations new consequent) := by
  have proved := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term guard) solver sound [] old
    (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
    (SourceGuards.applySubstitutions operations old consequent)
  rw [yes] at proved
  change SourceEntailment.Entails model (Domain sortDomain term guard old) _ _ at proved
  exact entails_yes model nullary laws sortDomain term guard recipes old new oldFound newFound accepted antecedent consequent
    leftNames rightNames proved

/-- A sound complete callback cannot refute a query certified by a sound sparse Yes. -/
theorem solver_yes_not_no (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (solver : SourceGuards.Entailment Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (yes : SourceGuards.decideWith solver [] old
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent) = .yes) :
    SourceGuards.decideWith solver [] new
      (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new antecedent))
      (SourceGuards.applySubstitutions operations new consequent) ≠ .no := by
  have proved := solver_yes_logical model nullary laws sortDomain term guard solver sound recipes old new oldFound newFound
    accepted antecedent consequent leftNames rightNames yes
  intro no
  have contrary := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term guard) solver sound [] new
    (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new antecedent))
    (SourceGuards.applySubstitutions operations new consequent)
  rw [no] at contrary
  exact contrary proved

end MicroCFTA.SourceQuotientQueries
