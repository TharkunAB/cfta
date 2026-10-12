import MicroCFTA.SourceKnownQueryTransport
import MicroCFTA.SourceQuotientHolds

/-!
# Refutation transport for positional Holds queries

The source No gate requires known active actual identities. The reverse
known-actual map also fixes positional contract names. Thus every sparse
Holds counterexample has a complete counterpart with all domains preserved.
-/
namespace MicroCFTA.SourceKnownHoldsTransport
open FullSyntax FormulaSubstitution SourceFormula SourceObservations SourceLogicalNames
open SourceQuotientEnvironment SourceQuotientQueries SourceKnownQueryTransport
open SourceGuards (Guard Path)

/-- The reverse known-actual map fixes all positional contract names. -/
theorem contract_fixed (term : Language.Term (Label Formula)) (guard : Guard Formula) (index : Nat) :
    renameName ((SourceKnownIdentityMap.names term guard).map Prod.swap) (SourceGuards.contractName index) =
      SourceGuards.contractName index := by
  by_cases used : SourceGuards.contractName index ∈ SourceGuards.usedNames operations (observe term) guard
  · exact SourceKnownIdentityMap.reverse_fixed term guard _ used
  · apply FormulaBinders.rename_absent
    intro present
    obtain ⟨swapped, swappedMember, key⟩ := List.mem_map.mp present
    obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp swappedMember
    subst swapped
    simp only [SourceKnownIdentityMap.names, List.mem_eraseDups] at pairMember
    obtain ⟨actual, actualMember, pairEq⟩ := List.mem_map.mp pairMember
    subst pair
    have actualMember := (List.mem_filter.mp actualMember).1
    cases allocated : (SourceGuards.allocated operations (observe term) (sameTerm operations term []) guard).lookup
        (SourceGuards.representative (observe term) (sameTerm operations term [])
          (SourceGuards.actuals (observe term) guard) actual) with
    | none =>
        have original : actual.name = SourceGuards.contractName index := by simpa [logicalName, allocated] using key
        exact used (original ▸ actual_name_used operations (observe term) guard actual actualMember)
    | some binding =>
        have fresh : binding.1 ∈ (SourceGuards.allocated operations (observe term) (sameTerm operations term []) guard).map
            (fun row => row.2.1) := List.mem_map.mpr ⟨_, lookup_member _ _ _ allocated, rfl⟩
        rw [allocated_fresh] at fresh
        have same : binding.1 = SourceGuards.contractName index := by simpa [logicalName, allocated] using key
        exact SourceContractNames.contract_not_fresh index _ _ (same ▸ fresh)

/-- The reverse environment keeps each positional value. -/
theorem contract_value (model : Interpretation Value) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (env : Name → Value) (index : Nat) :
    SourceKnownIdentityMap.lift model term guard env (SourceGuards.contractName index) = env (SourceGuards.contractName index) := by
  rw [SourceKnownIdentityMap.lift, FreshEnvironment.environment_names model env _
    (by simpa [List.map_map, Function.comp_def] using (SourceKnownIdentityMap.unique term guard).2), contract_fixed]

/-- Complete scoped positional values realize all known sparse scoped values. -/
theorem scoped_contract_value (model : Interpretation Value) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (known : Known old) (env : Name → Value) (index : Nat) :
    scopeEnvironment model (SourceKnownIdentityMap.lift model term guard env) new (SourceGuards.contractName index) =
      scopeEnvironment model env old (SourceGuards.contractName index) := by
  have paired := SourceKnownQueryTransport.stack_pair model term guard recipes old new oldFound newFound known env
  by_cases used : SourceGuards.contractName index ∈ SourceGuards.usedNames operations (observe term) guard
  · exact scopes_environment model _ _ env new old paired.1 (known_accepted new (complete_known term guard recipes new newFound))
      (SourceKnownIdentityMap.ambient_values model term guard env) paired.2 _ used
  · rw [scopes_absent, scopes_absent, contract_value]
    · intro scope member entry present same
      obtain ⟨newScope, _, relation⟩ := member_right paired.1 scope member
      obtain ⟨newEntry, _, row⟩ := member_right relation entry present
      exact used (same ▸ (row.newFormal ▸ row.formalLive))
    · intro scope member entry present same
      obtain ⟨oldScope, _, relation⟩ := member_left paired.1 scope member
      obtain ⟨oldEntry, _, row⟩ := member_left relation entry present
      exact used (same ▸ (row.oldFormal ▸ row.formalLive))

/-- The full positional contract realizes every known sparse assumption environment. -/
theorem contract_backward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (known : Known old) (targets : List Path)
    (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (env : Name → Value) :
    Holds model (SourceKnownIdentityMap.lift model term guard env)
      (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2) ↔
      Holds model env (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2) := by
  rw [scopes_semantics model nullary, scopes_semantics model nullary]
  apply SourceContractSemantics.contract_ext model nullary laws
  · intro value member name free
    have names := SourceHoldsQueries.observed_names guard (observe term) targets requested values found value member name free
    have used := SourceSemanticNames.ambient_used operations (observe term) guard name names
    have paired := SourceKnownQueryTransport.stack_pair model term guard recipes old new oldFound newFound known env
    exact scopes_environment model _ _ env new old paired.1 (known_accepted new (complete_known term guard recipes new newFound))
      (SourceKnownIdentityMap.ambient_values model term guard env) paired.2 name used
  · intro index bounded
    exact scoped_contract_value model term guard recipes old new oldFound newFound known env index

/-- Complete Holds antecedents transport backward under known active source identities. -/
theorem antecedent_backward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (known : Known old) (targets : List Path)
    (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (env : Name → Value) :
    Holds model (SourceKnownIdentityMap.lift model term guard env)
      (SourceGuards.withActualAssumptions operations new
        (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2)) ↔
      Holds model env (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2)) := by
  rw [actual_assumptions_semantics model laws, actual_assumptions_semantics model laws]
  exact and_congr (assumptions_backward model nullary term guard recipes old new oldFound newFound known env)
    (contract_backward model nullary laws term guard recipes old new oldFound newFound known targets requested values found env)

/-- Reverse transport keeps both positional domains and generated actual declarations. -/
theorem domain_backward (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old)
    (count : Nat) (env : Name → Value) (allowed : SourceQuotientHolds.Domain sortDomain term guard count old env) :
    SourceQuotientHolds.Domain sortDomain term guard count new (SourceKnownIdentityMap.lift model term guard env) := by
  have actuals := SourceKnownQueryTransport.domain_backward model sortDomain term guard recipes old new oldFound newFound known env
    ⟨allowed.1, allowed.2.2⟩
  refine ⟨actuals.1, ?_, actuals.2⟩
  intro index bounded
  rw [contract_value]
  exact allowed.2.1 index bounded

/-- Complete Holds entailment reflects back through known active actual identities. -/
theorem entails_backward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old)
    (targets : List Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (consequent : Formula)
    (names : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (proved : SourceEntailment.Entails model (SourceQuotientHolds.Domain sortDomain term guard targets.length new)
      (SourceGuards.withActualAssumptions operations new
        (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations new consequent)) :
    SourceEntailment.Entails model (SourceQuotientHolds.Domain sortDomain term guard targets.length old)
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent) := by
  intro env allowed assumed
  apply (formula_backward model nullary term guard recipes old new oldFound newFound known consequent names env).mp
  exact proved _ (domain_backward model sortDomain term guard recipes old new oldFound newFound known targets.length env allowed)
    ((antecedent_backward model nullary laws term guard recipes old new oldFound newFound known targets requested values found env).mpr assumed)

/-- A source Holds No refutes the complete mathematical query without a reverse backend contract. -/
theorem solver_no_logical (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (solver : SourceGuards.Entailment Formula) (sound : SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (targets : List Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany (observe term) targets = some values) (consequent : Formula)
    (names : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (no : SourceGuards.decideWith solver
      ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent) = .no) :
    ¬SourceEntailment.Entails model (SourceQuotientHolds.Domain sortDomain term guard targets.length new)
      (SourceGuards.withActualAssumptions operations new
        (SourceGuards.applySubstitutions operations new (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations new consequent) := by
  have known := no_known solver _ old _ _ no
  have support := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term guard) solver sound
    ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
    (SourceGuards.withActualAssumptions operations old
      (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
    (SourceGuards.applySubstitutions operations old consequent)
  rw [no] at support
  intro proved
  have reflected := entails_backward model nullary laws sortDomain term guard recipes old new oldFound newFound known
    targets requested values found consequent names proved
  apply support
  intro env allowed assumed
  exact reflected env ⟨allowed.1, (SourceHoldsQueries.domain_exact sortDomain targets.length old env).mpr allowed.2⟩ assumed

end MicroCFTA.SourceKnownHoldsTransport
