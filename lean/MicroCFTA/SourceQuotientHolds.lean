import MicroCFTA.SourceQuotientQueries

/-!
# Positional Holds queries under actual identification

Contract names use a different prefix from actual names. Their values remain
fixed by the identity quotient even when no requirement mentions them.
The proof includes repeated-path aliases and every positional declaration.
-/
namespace MicroCFTA.SourceQuotientHolds
open FullSyntax FormulaSubstitution SourceFormula SourceQuotientEnvironment SourceQuotientQueries
open SourceGuards (Path Guard Resolved)
open SourceObservations

/-- The actual quotient keeps every positional contract variable fixed. -/
theorem contract_fixed (term : Language.Term (Label Formula)) (guard : Guard Formula) (index : Nat) :
    renameName (SourceIdentityMap.names operations term guard) (SourceGuards.contractName index) = SourceGuards.contractName index := by
  by_cases used : SourceGuards.contractName index ∈ SourceGuards.usedNames operations (observe term) guard
  · exact SourceIdentityMap.used_fixed operations term guard _ used
  · apply FormulaBinders.rename_absent
    intro present
    obtain ⟨pair, member, key⟩ := List.mem_map.mp present
    simp only [SourceIdentityMap.names, List.mem_eraseDups] at member
    obtain ⟨actual, actualMember, pairEq⟩ := List.mem_map.mp member
    subst pair
    dsimp only at key
    cases allocated : (SourceGuards.allocated operations (observe term) (sameShape operations (observe term) []) guard).lookup
        (SourceGuards.representative (observe term) (sameShape operations (observe term) [])
          (SourceGuards.actuals (observe term) guard) actual) with
    | none =>
        have original : actual.name = SourceGuards.contractName index := by simpa [SourceLogicalNames.logicalName, allocated] using key
        exact used (original ▸ SourceLogicalNames.actual_name_used operations (observe term) guard actual actualMember)
    | some binding =>
        have fresh : binding.1 ∈ (SourceGuards.allocated operations (observe term) (sameShape operations (observe term) []) guard).map
            (fun row => row.2.1) := List.mem_map.mpr ⟨_, SourceLogicalNames.lookup_member _ _ _ allocated, rfl⟩
        rw [SourceLogicalNames.allocated_fresh] at fresh
        have same : binding.1 = SourceGuards.contractName index := by simpa [SourceLogicalNames.logicalName, allocated] using key
        exact SourceContractNames.contract_not_fresh index _ _ (same ▸ fresh)

/-- Pullback of a complete environment retains each positional value. -/
theorem contract_value (model : Interpretation Value) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (env : Name → Value) (index : Nat) :
    renamedEnvironment model env (SourceIdentityMap.names operations term guard) (SourceGuards.contractName index) =
      env (SourceGuards.contractName index) := by
  rw [FreshEnvironment.environment_names model env _ (SourceIdentityMap.keys_unique operations term guard), contract_fixed]

/-- Source scopes preserve the corresponding positional values, including names absent from the original avoid set. -/
theorem scoped_contract_value (model : Interpretation Value) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (env : Name → Value) (index : Nat) :
    scopeEnvironment model (renamedEnvironment model env (SourceIdentityMap.names operations term guard)) old
        (SourceGuards.contractName index) =
      scopeEnvironment model env new (SourceGuards.contractName index) := by
  have paired := stack_pair model term guard recipes old new oldFound newFound env
  by_cases used : SourceGuards.contractName index ∈ SourceGuards.usedNames operations (observe term) guard
  · exact scopes_environment model _ _ env old new paired.1 accepted (SourceIdentityQuotient.ambient_values model term guard env)
      paired.2 _ used
  · rw [scopes_absent, scopes_absent, contract_value]
    · intro scope member entry present same
      obtain ⟨oldScope, _, relation⟩ := member_right paired.1 scope member
      obtain ⟨oldEntry, _, row⟩ := member_right relation entry present
      exact used (same ▸ (row.newFormal ▸ row.formalLive))
    · intro scope member entry present same
      obtain ⟨newScope, _, relation⟩ := member_left paired.1 scope member
      obtain ⟨newEntry, _, row⟩ := member_left relation entry present
      exact used (same ▸ (row.oldFormal ▸ row.formalLive))

/-- The entire generated contract formula transports through accepted source scopes. -/
theorem contract_forward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (targets : List Path)
    (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (env : Name → Value) :
    Holds model (renamedEnvironment model env (SourceIdentityMap.names operations term guard))
      (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2) ↔
      Holds model env (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2) := by
  rw [scopes_semantics model nullary, scopes_semantics model nullary]
  apply SourceContractSemantics.contract_ext model nullary laws
  · intro value member name free
    have names := SourceHoldsQueries.observed_names guard (observe term) targets requested values found value member name free
    have used := SourceSemanticNames.ambient_used operations (observe term) guard name names
    have paired := stack_pair model term guard recipes old new oldFound newFound env
    exact scopes_environment model _ _ env old new paired.1 accepted (SourceIdentityQuotient.ambient_values model term guard env)
      paired.2 name used
  · intro index bounded
    exact scoped_contract_value model term guard recipes old new oldFound newFound accepted env index

/-- Positional and ambient actual assumptions form exactly the transported source Holds antecedent. -/
theorem antecedent_forward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (targets : List Path)
    (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (env : Name → Value) :
    Holds model (renamedEnvironment model env (SourceIdentityMap.names operations term guard))
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2)) ↔
      Holds model env (SourceGuards.withActualAssumptions operations new
        (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2)) := by
  rw [actual_assumptions_semantics model laws, actual_assumptions_semantics model laws]
  exact and_congr (assumptions_forward model nullary term guard recipes old new oldFound newFound env)
    (contract_forward model nullary laws term guard recipes old new oldFound newFound accepted targets requested values found env)

/-- Holds includes every positional value domain as well as the ambient and actual domains. -/
def Domain (sortDomain : Name → Value → Prop) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (count : Nat) (scopes : List Scope) (env : Name → Value) : Prop :=
  AmbientDomain sortDomain term guard env ∧ SourceHoldsQueries.Domain sortDomain count scopes env

/-- Generated positional declarations survive even when complete actual declarations disappear. -/
theorem domain_forward (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (count : Nat) (env : Name → Value)
    (allowed : Domain sortDomain term guard count new env) :
    Domain sortDomain term guard count old (renamedEnvironment model env (SourceIdentityMap.names operations term guard)) := by
  have actuals := SourceQuotientQueries.domain_forward model sortDomain term guard recipes old new oldFound newFound env
    ⟨allowed.1, allowed.2.2⟩
  refine ⟨actuals.1, ?_, actuals.2⟩
  intro index bounded
  rw [contract_value]
  exact allowed.2.1 index bounded

/-- Positive source Holds entailment survives ambiguous complete-actual identification. -/
theorem entails_yes (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (targets : List Path)
    (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (consequent : Formula)
    (names : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (proved : SourceEntailment.Entails model (Domain sortDomain term guard targets.length old)
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent)) :
    SourceEntailment.Entails model (Domain sortDomain term guard targets.length new)
      (SourceGuards.withActualAssumptions operations new
        (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations new consequent) := by
  have identified := SourceEntailment.rename_yes model nullary
    (Domain sortDomain term guard targets.length old) (Domain sortDomain term guard targets.length new)
    (SourceIdentityMap.names operations term guard) _ _
    (domain_forward model sortDomain term guard recipes old new oldFound newFound targets.length) proved
  intro env allowed assumed
  apply (formula_forward model nullary term guard recipes old new oldFound newFound accepted consequent names env).mp
  apply (substitute_semantics model nullary env _ _).mp
  apply identified env allowed
  apply (substitute_semantics model nullary env _ _).mpr
  exact (antecedent_forward model nullary laws term guard recipes old new oldFound newFound accepted
    targets requested values found env).mpr assumed

/-- A sound sparse Holds Yes certifies its complete logical query without a completeness assumption on the solver. -/
theorem solver_yes_logical (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (solver : SourceGuards.Entailment Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (targets : List Path)
    (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (consequent : Formula)
    (names : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (yes : SourceGuards.decideWith solver
      ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent) = .yes) :
    SourceEntailment.Entails model (Domain sortDomain term guard targets.length new)
      (SourceGuards.withActualAssumptions operations new
        (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations new consequent) := by
  have proved := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term guard) solver sound
    ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
    (SourceGuards.withActualAssumptions operations old
      (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
    (SourceGuards.applySubstitutions operations old consequent)
  rw [yes] at proved
  apply entails_yes model nullary laws sortDomain term guard recipes old new oldFound newFound accepted
    targets requested values found consequent names
  intro env allowed assumed
  exact proved env ⟨allowed.1, (SourceHoldsQueries.domain_exact sortDomain targets.length old env).mp allowed.2⟩ assumed

/-- A sound complete callback cannot return No for a Holds query certified by sparse Yes. -/
theorem solver_yes_not_no (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (solver : SourceGuards.Entailment Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (targets : List Path)
    (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (consequent : Formula)
    (names : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (yes : SourceGuards.decideWith solver
      ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent) = .yes) :
    SourceGuards.decideWith solver
      ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) new
      (SourceGuards.withActualAssumptions operations new
        (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations new consequent) ≠ .no := by
  have proved := solver_yes_logical model nullary laws sortDomain term guard solver sound recipes old new oldFound newFound
    accepted targets requested values found consequent names yes
  intro no
  have contrary := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term guard) solver sound
    ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) new
    (SourceGuards.withActualAssumptions operations new
      (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2))
    (SourceGuards.applySubstitutions operations new consequent)
  rw [no] at contrary
  apply contrary
  intro env allowed assumed
  exact proved env ⟨allowed.1, (SourceHoldsQueries.domain_exact sortDomain targets.length new env).mpr allowed.2⟩ assumed

end MicroCFTA.SourceQuotientHolds
