import MicroCFTA.SourceKnownIdentityMap

/-!
# Refutation transport through known active scopes

The source can return No only when all active identity flags are known.
The restricted identity map then supplies a reverse environment. This proves
negative Entails transport without an external refutation-stability premise.
-/
namespace MicroCFTA.SourceKnownQueryTransport
open FullSyntax FormulaSubstitution SourceFormula SourceObservations
open SourceQuotientEnvironment SourceQuotientQueries SourceIdentityQuotient
open SourceGuards (Guard Resolved Substitution)

/-- Every active source actual identity is known. -/
def Known (scopes : List Scope) : Prop := scopes.all (fun scope => scope.all Resolved.identityKnown) = true

/-- Known flags can be read at every nested source record. -/
theorem known_entry (scopes : List Scope) (known : Known scopes) (scope : Scope) (member : scope ∈ scopes)
    (entry : Resolved Formula) (present : entry ∈ scope) : entry.identityKnown = true :=
  List.all_eq_true.mp (List.all_eq_true.mp known scope member) entry present

/-- A source No itself establishes the known-scope invariant. -/
theorem no_known (solver : SourceGuards.Entailment Formula) (bindings : List (Name × Name))
    (scopes : List Scope) (antecedent consequent : Formula)
    (no : SourceGuards.decideWith solver bindings scopes antecedent consequent = .no) : Known scopes := by
  cases result : scopes.all (fun scope => scope.all Resolved.identityKnown) with
  | false => exact False.elim (SourceGuards.ambiguous_never_no solver bindings scopes antecedent consequent result no)
  | true => exact result

/-- Complete source resolution always records known actual identities. -/
theorem complete_known (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe)
    (scopes : List Scope) (resolved : Resolves term guard (sameTerm operations term []) recipes scopes) : Known scopes := by
  induction resolved with
  | nil => rfl
  | @cons recipe scope recipes scopes head tail ih =>
      have found := head.1
      unfold resolve at found
      change SourceGuards.resolveMany operations (observe term) _
        (SourceGuards.ambiguous (observe term) (sameTerm operations term []) guard) recipe = some scope at found
      rw [ActualQuotient.complete_ambiguity_empty] at found
      have each := SourceKnownScopes.resolveMany_known operations (observe term) _ recipe scope found
      simp only [Known, List.all_cons, Bool.and_eq_true]
      exact ⟨each, ih⟩

/-- Known active identities pass both current source scope checks. -/
theorem known_accepted (scopes : List Scope) (known : Known scopes) : Accepted scopes := by
  induction scopes with
  | nil => trivial
  | cons scope outer ih =>
      have first : scope.all Resolved.identityKnown = true := List.all_eq_true.mp known scope (by simp)
      have rest : Known outer := by
        apply List.all_eq_true.mpr
        intro next member
        exact List.all_eq_true.mp known next (by simp [member])
      refine ⟨SourceSubstitutionPrecedence.known_precedence scope first, ?_, ih rest⟩
      apply List.any_eq_false.mpr
      intro entry member
      simp [SourceEnclosingRenames.renamedByEnclosing, List.all_eq_true.mp first entry member]

/-- Reverse the direction of an ordered relation. -/
theorem reverse_relation (related : Language.All₂ relation old new) : Language.All₂ (fun b a => relation a b) new old := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

/-- A known source record identifies a path in the restricted actual map. -/
theorem resolved_known (term : Language.Term (Label Formula)) (guard : Guard Formula) (entry : Substitution)
    (old : Resolved Formula)
    (found : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (known : old.identityKnown = true) :
    entry.actual ∉ SourceGuards.ambiguous (observe term) (sameShape operations (observe term) []) guard := by
  intro member
  have unknown := (SourceActuals.resolve_unknown operations (observe term) _ _ entry old found).mpr member
  simp [known] at unknown

/-- The reverse environment supplies the original sparse value for every active known actual. -/
theorem row_values (model : Interpretation Value) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (entry : Substitution) (requested : entry.actual ∈ SourceGuards.actualPaths guard) (old new : Resolved Formula)
    (oldFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).2 entry = some new)
    (known : old.identityKnown = true) (env : Name → Value) :
    SourceKnownIdentityMap.lift model term guard env new.replacement.2 = env old.replacement.2 := by
  have isKnown := resolved_known term guard entry old oldFound known
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry old oldFound
  rw [resolved_row term guard _ entry actual formal requested atActual atFormal old oldFound,
    resolved_row term guard _ entry actual formal requested atActual atFormal new newFound]
  exact SourceKnownIdentityMap.actual_value model term guard env _
    (actual_member (observe term) guard entry.actual actual requested atActual) isKnown

/-- Every active scope inherits the reverse local-record and actual-value relations. -/
theorem stack_pair (model : Interpretation Value) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old) (env : Name → Value) :
    Language.All₂ (Language.All₂ (Pair (SourceGuards.usedNames operations (observe term) guard))) new old ∧
    Language.All₂ (Language.All₂ (fun a b => SourceKnownIdentityMap.lift model term guard env a.replacement.2 = env b.replacement.2)) new old := by
  have pairs := stack_relation term guard _ _ recipes old new oldFound newFound
    (fun a b => a.identityKnown = true → Pair (SourceGuards.usedNames operations (observe term) guard) b a ∧
      SourceKnownIdentityMap.lift model term guard env b.replacement.2 = env a.replacement.2) (by
      intro recipe requested entry member a b first second flag
      exact ⟨SourceKnownIdentityMap.pair_reverse
        (resolve_pair term guard entry (requested entry member).1 (requested entry member).2 a b first second) flag,
        row_values model term guard entry (requested entry member).1 a b first second flag env⟩)
  have each : Language.All₂ (Language.All₂ (fun b a => Pair (SourceGuards.usedNames operations (observe term) guard) b a ∧
      SourceKnownIdentityMap.lift model term guard env b.replacement.2 = env a.replacement.2)) new old := by
    apply reverse_relation
    apply map_relation pairs
    intro scope member other otherMember related
    apply reverse_relation
    apply map_relation related
    intro a present b otherPresent row
    exact row (known_entry old known scope member a present)
  exact ⟨each.imp (fun _ _ rows => rows.imp (fun _ _ row => row.1)),
    each.imp (fun _ _ rows => rows.imp (fun _ _ row => row.2))⟩

/-- Complete scoped formulas lift back to every sparse environment when all active identities are known. -/
theorem formula_backward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old)
    (formula : Formula) (names : ∀ name ∈ formulaNames formula, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (env : Name → Value) :
    Holds model (SourceKnownIdentityMap.lift model term guard env) (SourceGuards.applySubstitutions operations new formula) ↔
      Holds model env (SourceGuards.applySubstitutions operations old formula) := by
  have paired := stack_pair model term guard recipes old new oldFound newFound known env
  exact scoped_formula model nullary _ _ env new old paired.1 (stack_coherent term guard _ recipes old oldFound) (known_accepted new (complete_known term guard recipes new newFound))
    (SourceKnownIdentityMap.ambient_values model term guard env) paired.2 formula names

/-- Ambient actual assumptions also reverse under known active identities. -/
theorem row_assumption (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (entry : Substitution)
    (requested : entry.actual ∈ SourceGuards.actualPaths guard) (old new : Resolved Formula)
    (oldFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).2 entry = some new)
    (known : old.identityKnown = true) (env : Name → Value) :
    Holds model (SourceKnownIdentityMap.lift model term guard env) new.actualAssumption ↔ Holds model env old.actualAssumption := by
  have isKnown := resolved_known term guard entry old oldFound known
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry old oldFound
  rw [resolved_row term guard _ entry actual formal requested atActual atFormal old oldFound,
    resolved_row term guard _ entry actual formal requested atActual atFormal new newFound]
  apply SourceActualAssumptions.assumption_equivalent model nullary
  · intro name member
    apply SourceKnownIdentityMap.ambient_values model term guard env
    exact SourceSemanticNames.free_used operations (observe term) guard entry.actual actual name
      (SourceReadAgreement.sensitive_requested guard _ (SourceIdentityReads.actual_sensitive guard _ requested)) atActual
      (by simpa [operations, FullSyntax.freeNames] using member)
  · exact SourceKnownIdentityMap.actual_value model term guard env _
      (actual_member (observe term) guard entry.actual actual requested atActual) isKnown

/-- The complete conjunction of actual assumptions realizes every known sparse assumption environment. -/
theorem assumptions_backward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old) (env : Name → Value) :
    (∀ scope ∈ new, ∀ entry ∈ scope, Holds model (SourceKnownIdentityMap.lift model term guard env) entry.actualAssumption) ↔
      (∀ scope ∈ old, ∀ entry ∈ scope, Holds model env entry.actualAssumption) := by
  have pairs := stack_relation term guard _ _ recipes old new oldFound newFound
    (fun a b => a.identityKnown = true → (Holds model (SourceKnownIdentityMap.lift model term guard env) b.actualAssumption ↔
      Holds model env a.actualAssumption)) (by
      intro recipe requested entry member a b first second flag
      exact row_assumption model nullary term guard entry (requested entry member).1 a b first second flag env)
  apply all_related
  apply reverse_relation
  apply map_relation pairs
  intro scope member other otherMember related
  apply all_related
  apply reverse_relation
  apply map_relation related
  intro a present b otherPresent row
  exact row (known_entry old known scope member a present)

/-- All complete antecedent parts lift back through the accepted known scopes. -/
theorem antecedent_backward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old)
    (formula : Formula) (names : ∀ name ∈ formulaNames formula, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (env : Name → Value) :
    Holds model (SourceKnownIdentityMap.lift model term guard env)
      (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new formula)) ↔
    Holds model env (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old formula)) := by
  rw [actual_assumptions_semantics model laws, actual_assumptions_semantics model laws]
  exact and_congr (assumptions_backward model nullary term guard recipes old new oldFound newFound known env)
    (formula_backward model nullary term guard recipes old new oldFound newFound known formula names env)

/-- Every complete generated declaration lifts to its known sparse domain. -/
theorem row_domain_backward (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (entry : Substitution)
    (requested : entry.actual ∈ SourceGuards.actualPaths guard) (old new : Resolved Formula)
    (oldFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations (observe term)
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).1
      (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).2 entry = some new)
    (known : old.identityKnown = true) (env : Name → Value)
    (declared : ∀ binding, old.declaration = some binding → sortDomain binding.2 (env binding.1)) :
    ∀ binding, new.declaration = some binding → sortDomain binding.2
      (SourceKnownIdentityMap.lift model term guard env binding.1) := by
  intro binding found
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry old oldFound
  have newFields := resolved_declaration term guard _ entry actual formal requested atActual atFormal new newFound binding found
  rw [newFields.1, newFields.2, row_values model term guard entry requested old new oldFound newFound known env]
  cases present : old.declaration with
  | none =>
      have oldRow := resolved_row term guard _ entry actual formal requested atActual atFormal old oldFound
      rw [oldRow] at present
      have member := actual_member (observe term) guard entry.actual actual requested atActual
      have before : (SourceGuards.allocated operations (observe term) (sameShape operations (observe term) []) guard).lookup
          (SourceGuards.representative (observe term) (sameShape operations (observe term) [])
            (SourceGuards.actuals (observe term) guard) ⟨entry.actual, actual.name, actual.refinement⟩) = none := by
        rw [← SourceLogicalNames.copied_lookup operations (observe term) _ guard _ member]
        exact present
      have after := SourceIdentityMap.unallocated_complete operations term guard _ member before
      have impossible : new.declaration = none := by
        rw [resolved_row term guard _ entry actual formal requested atActual atFormal new newFound]
        change (SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) guard).1.lookup entry.actual = none
        rw [SourceLogicalNames.copied_lookup operations (observe term) _ guard _ member]
        exact after
      simp [impossible] at found
  | some other =>
      have oldFields := resolved_declaration term guard _ entry actual formal requested atActual atFormal old oldFound other present
      simpa only [oldFields.1, oldFields.2] using declared other present

/-- The constructed complete environment realizes all sparse ambient and generated domains. -/
theorem domain_backward (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old) (env : Name → Value)
    (allowed : Domain sortDomain term guard old env) :
    Domain sortDomain term guard new (SourceKnownIdentityMap.lift model term guard env) := by
  constructor
  · intro name member
    rw [SourceKnownIdentityMap.ambient_values model term guard env name member]
    exact allowed.1 name member
  · apply (SourceSortedQueries.domain_iff sortDomain new _).mpr
    have pairs := stack_relation term guard _ _ recipes old new oldFound newFound
      (fun a b => a.identityKnown = true →
        (∀ binding, a.declaration = some binding → sortDomain binding.2 (env binding.1)) →
        ∀ binding, b.declaration = some binding → sortDomain binding.2
          (SourceKnownIdentityMap.lift model term guard env binding.1)) (by
          intro recipe requested entry member a b first second flag
          exact row_domain_backward model sortDomain term guard entry (requested entry member).1 a b first second flag env)
    intro scope member entry present
    obtain ⟨other, otherMember, related⟩ := member_right pairs scope member
    obtain ⟨oldEntry, oldMember, row⟩ := member_right related entry present
    exact row (known_entry old known other otherMember oldEntry oldMember)
      ((SourceSortedQueries.domain_iff sortDomain old env).mp allowed.2 other otherMember oldEntry oldMember)

/-- Complete entailment reflects back to known active source scopes, without global table unambiguity. -/
theorem entails_backward (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new) (known : Known old)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (proved : SourceEntailment.Entails model (Domain sortDomain term guard new)
      (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new antecedent))
      (SourceGuards.applySubstitutions operations new consequent)) :
    SourceEntailment.Entails model (Domain sortDomain term guard old)
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent) := by
  intro env allowed assumed
  apply (formula_backward model nullary term guard recipes old new oldFound newFound known consequent rightNames env).mp
  exact proved (SourceKnownIdentityMap.lift model term guard env)
    (domain_backward model sortDomain term guard recipes old new oldFound newFound known env allowed)
    ((antecedent_backward model nullary laws term guard recipes old new oldFound newFound known antecedent leftNames env).mpr assumed)

/-- A sound sparse No refutes the complete logical query because the runtime forces known active scopes. -/
theorem solver_no_logical (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (solver : SourceGuards.Entailment Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceGuards.usedNames operations (observe term) guard)
    (no : SourceGuards.decideWith solver [] old
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent) = .no) :
    ¬SourceEntailment.Entails model (Domain sortDomain term guard new)
      (SourceGuards.withActualAssumptions operations new (SourceGuards.applySubstitutions operations new antecedent))
      (SourceGuards.applySubstitutions operations new consequent) := by
  have known := no_known solver [] old _ _ no
  have disproved := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term guard) solver sound [] old
    (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
    (SourceGuards.applySubstitutions operations old consequent)
  rw [no] at disproved
  intro proved
  exact disproved (entails_backward model nullary laws sortDomain term guard recipes old new oldFound newFound known
    antecedent consequent leftNames rightNames proved)

end MicroCFTA.SourceKnownQueryTransport
