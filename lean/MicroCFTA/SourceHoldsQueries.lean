import MicroCFTA.SourceContractSemantics

/-!
# Complete source Holds query transport

This connects the source observation list, repeated-path aliases, nested
substitution stack, actual assumptions, and generated sort declarations.
-/
namespace MicroCFTA.SourceHoldsQueries
open FullSyntax FormulaSubstitution SourceFormula SourceScopeStack SourceScopeQueries

private theorem aligned_stacks (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other) :
    Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned (SourceFreshTables.tableRenaming operations guard first second))) scopes other := by
  induction resolved generalizing other with
  | nil => cases otherResolved; exact .nil
  | @cons recipe scope recipes scopes head tail ih =>
      cases otherResolved with
      | @cons _ otherScope _ _ otherHead otherTail =>
          have each := SourceResolvedTables.resolveMany_aligned operations guard first second reads recipe head.2
          change SourceResolvedTables.OptionRel _ (resolve guard first recipe) (resolve guard second recipe) at each
          rw [head.1, otherHead.1] at each
          exact .cons each (ih _ otherTail)

/-- Every source contract refinement came from one requested guard path. -/
theorem observed_names (guard : SourceGuards.Guard Formula) (observed : SourceGuards.Observations Formula)
    (targets : List SourceGuards.Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values : List (SourceGuards.Observed Formula)) (found : SourceGuards.observeMany observed targets = some values) :
    ∀ value ∈ values, ∀ name ∈ formulaNames value.refinement, name ∈ SourceSemanticNames.ambient operations observed guard := by
  induction targets generalizing values with
  | nil => simp [SourceGuards.observeMany] at found; subst values; simp
  | cons target rest ih =>
      cases one : observed target <;> cases tail : SourceGuards.observeMany observed rest <;>
        simp [SourceGuards.observeMany, one, tail] at found
      subst values
      intro value member name free
      rcases List.mem_cons.mp member with rfl | later
      · exact observed_formula_names guard observed target value (requested target (by simp)) one name free
      · exact ih (fun path member => requested path (by simp [member])) _ tail value later name free

/-- All parts of the source contract remain equivalent after the full nested scope fold. -/
theorem contract_related (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (targets : List SourceGuards.Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values otherValues : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany first targets = some values) (otherFound : SourceGuards.observeMany second targets = some otherValues)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceContractNames.live guard first targets.length) firstEnv secondEnv) :
    Holds model firstEnv (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2) ↔
      Holds model secondEnv (SourceGuards.applySubstitutions operations other (SourceGuards.contract operations targets otherValues).2) := by
  have same := SourceReadAgreement.observeMany_refinements first second targets
    (fun target member => reads.refinements target (requested target member))
  rw [found, otherFound] at same
  have prepared := SourceReadAgreement.contract_refinements operations targets values otherValues (Option.some.inj same)
  rw [← prepared, scopes_semantics model nullary, scopes_semantics model nullary]
  have scopeRelation := SourceScopeEnvironment.scopes_commute model _ _ (SourceContractNames.live_injective guard first second reads targets.length)
    firstEnv secondEnv related scopes other (aligned_stacks guard first second reads recipes scopes other resolved otherResolved)
    (by
      intro scope member entry present
      have closed := SourceScopeStack.closed guard first second recipes scopes resolved scope member entry present
      exact ⟨List.mem_append_left _ closed.1, List.mem_append_left _ closed.2.1, closed.2.2⟩)
  apply SourceContractSemantics.contract_ext model nullary laws
  · intro value member name free
    have ambient := observed_names guard first targets requested values found value member name free
    have exact := scopeRelation name (List.mem_append_left _ (List.mem_append_left _ ambient))
    simpa only [SourceSemanticNames.ambient_fixed operations guard first second name ambient] using exact
  · intro index bounded
    have exact := scopeRelation (SourceGuards.contractName index)
      (List.mem_append_right _ (List.mem_map.mpr ⟨index, List.mem_range.mpr bounded, rfl⟩))
    simpa only [SourceContractNames.contract_fixed guard first second index] using exact

/-- Holds adds positional value-sort declarations to the exact scope declaration list. -/
def Domain (sortDomain : Name → Value → Prop) (count : Nat) (scopes : List Scope) (env : Name → Value) : Prop :=
  (∀ index < count, sortDomain SourceGuards.valueName (env (SourceGuards.contractName index))) ∧
    SourceSortedQueries.Domain sortDomain scopes env

/-- The conjunction domain is exactly the source appended and deduplicated declaration list. -/
theorem domain_exact (sortDomain : Name → Value → Prop) (count : Nat) (scopes : List Scope) (env : Name → Value) :
    Domain sortDomain count scopes env ↔
      ∀ binding ∈ (((List.range count).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) ++
        scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups, sortDomain binding.2 (env binding.1) := by
  simp only [Domain, SourceSortedQueries.Domain, SourceSortedQueries.declarations, List.mem_eraseDups,
    List.mem_append]
  constructor
  · rintro ⟨formals, actuals⟩ binding (formal | actual)
    · obtain ⟨index, bounded, rfl⟩ := List.mem_map.mp formal
      exact formals index (List.mem_range.mp bounded)
    · exact actuals binding actual
  · intro all
    exact ⟨fun index bounded => all _ (Or.inl (List.mem_map.mpr ⟨index, List.mem_range.mpr bounded, rfl⟩)),
      fun binding member => all binding (Or.inr member)⟩

/-- Both positional and actual declaration domains follow the concrete source name map. -/
theorem domain_related (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (count : Nat) (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceContractNames.live guard first count) firstEnv secondEnv) :
    Domain sortDomain count scopes firstEnv ↔ Domain sortDomain count other secondEnv := by
  apply and_congr _ (SourceSortedQueries.domain_related sortDomain guard first second reads recipes scopes other
    resolved otherResolved firstEnv secondEnv (fun name member => related name (List.mem_append_left _ member)))
  have equal : ∀ index < count, firstEnv (SourceGuards.contractName index) = secondEnv (SourceGuards.contractName index) := by
    intro index bounded
    have exact := related (SourceGuards.contractName index)
      (List.mem_append_right _ (List.mem_map.mpr ⟨index, List.mem_range.mpr bounded, rfl⟩))
    simpa only [SourceContractNames.contract_fixed guard first second index] using exact
  exact ⟨fun all index bounded => equal index bounded ▸ all index bounded,
    fun all index bounded => (equal index bounded).symm ▸ all index bounded⟩

/-- The exact Holds antecedent retains all contract parts and all ambient actual assumptions. -/
theorem antecedent_related (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (targets : List SourceGuards.Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values otherValues : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany first targets = some values) (otherFound : SourceGuards.observeMany second targets = some otherValues)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceContractNames.live guard first targets.length) firstEnv secondEnv) :
    Holds model firstEnv (SourceGuards.withActualAssumptions operations scopes
      (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2)) ↔
      Holds model secondEnv (SourceGuards.withActualAssumptions operations other
        (SourceGuards.applySubstitutions operations other (SourceGuards.contract operations targets otherValues).2)) := by
  rw [actual_assumptions_semantics model laws, actual_assumptions_semantics model laws]
  exact and_congr (stack_actuals_related model nullary guard first second reads recipes scopes other resolved otherResolved
    firstEnv secondEnv (fun name member => related name (List.mem_append_left _ member)))
    (contract_related model nullary laws guard first second reads recipes scopes other resolved otherResolved
      targets requested values otherValues found otherFound firstEnv secondEnv related)

/-- Source Holds queries preserve mathematical entailment with their complete generated declaration lists. -/
theorem query_iff (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (targets : List SourceGuards.Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values otherValues : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany first targets = some values) (otherFound : SourceGuards.observeMany second targets = some otherValues)
    (consequent : Formula)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard) :
    SourceEntailment.Entails model (Domain sortDomain targets.length scopes)
      (SourceGuards.withActualAssumptions operations scopes
        (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations scopes consequent) ↔
    SourceEntailment.Entails model (Domain sortDomain targets.length other)
      (SourceGuards.withActualAssumptions operations other
        (SourceGuards.applySubstitutions operations other (SourceGuards.contract operations targets otherValues).2))
      (SourceGuards.applySubstitutions operations other consequent) := by
  constructor
  · intro proved env allowed assumed
    have related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
        (SourceContractNames.live guard first targets.length)
        (renamedEnvironment model env (SourceFreshTables.tableRenaming operations guard first second)) env := by
      intro name _
      exact FreshEnvironment.environment_names model env _ (SourceFreshTables.renaming_unique operations guard first second).1 name
    have smaller := fun name member => related name (List.mem_append_left _ member)
    exact (formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
      _ env smaller consequent rightNames).mp
      (proved _ ((domain_related sortDomain guard first second reads recipes scopes other resolved otherResolved _ _ env related).mpr allowed)
        ((antecedent_related model nullary laws guard first second reads recipes scopes other resolved otherResolved
          targets requested values otherValues found otherFound _ env related).mpr assumed))
  · intro proved env allowed assumed
    have related := SourceContractNames.lift_related model guard first second reads targets.length env
    have smaller := fun name member => related name (List.mem_append_left _ member)
    exact (formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
      env _ smaller consequent rightNames).mpr
      (proved _ ((domain_related sortDomain guard first second reads recipes scopes other resolved otherResolved _ env _ related).mp allowed)
        ((antecedent_related model nullary laws guard first second reads recipes scopes other resolved otherResolved
          targets requested values otherValues found otherFound env _ related).mp assumed))

end MicroCFTA.SourceHoldsQueries
