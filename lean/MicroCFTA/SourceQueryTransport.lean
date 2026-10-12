import MicroCFTA.SourceHoldsQueries

/-!
# Explicit solver stability under constructed name transport

Mathematical query equivalence is proved separately from exact solver verdict
agreement. The latter is an additional backend contract. It is not asserted
for the supplied timeout-limited backend or its ambient declaration context.
-/
namespace MicroCFTA.SourceQueryTransport
open FullSyntax SourceFormula SourceScopeStack SourceScopeQueries

/-- The complete arguments of one source solver call. -/
structure Query where
  declarations : List (Name × Name)
  antecedent : Formula
  consequent : Formula

/-- Generated declarations keep the domain selected by their original name. -/
def Domain (sortDomain : Name → Value → Prop) (query : Query) (env : Name → Value) : Prop :=
  ∀ binding ∈ query.declarations, sortDomain binding.2 (env binding.1)

/-- Compare declaration domains and both query formulas at corresponding environments. -/
def Agree (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (first second : Query) (firstEnv secondEnv : Name → Value) : Prop :=
  (Domain sortDomain first firstEnv ↔ Domain sortDomain second secondEnv) ∧
  (Holds model firstEnv first.antecedent ↔ Holds model secondEnv second.antecedent) ∧
  (Holds model firstEnv first.consequent ↔ Holds model secondEnv second.consequent)

/-- Both environment directions use the concrete finite source name map. -/
structure Transport (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (renamed : List (Name × Name)) (first second : Query) : Prop where
  forward : ∀ env, Agree model sortDomain first second (renamedEnvironment model env renamed) env
  backward : ∀ env, Agree model sortDomain first second env (FreshEnvironment.liftEnvironment renamed env)

/-- The constructed transport proves mathematical entailment in both directions. -/
theorem entails_iff (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (renamed : List (Name × Name)) (first second : Query)
    (transport : Transport model sortDomain renamed first second) :
    SourceEntailment.Entails model (Domain sortDomain first) first.antecedent first.consequent ↔
      SourceEntailment.Entails model (Domain sortDomain second) second.antecedent second.consequent := by
  constructor
  · intro proved env allowed assumed
    have related := transport.forward env
    exact related.2.2.mp (proved _ (related.1.mpr allowed) (related.2.1.mpr assumed))
  · intro proved env allowed assumed
    have related := transport.backward env
    exact related.2.2.mpr (proved _ (related.1.mp allowed) (related.2.1.mp assumed))

/-- Soundness transports mathematical evidence without assuming identical solver verdicts. -/
theorem supports_transport (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (renamed : List (Name × Name)) (first second : Query)
    (transport : Transport model sortDomain renamed first second) (verdict : Guards.Verdict)
    (sound : Guards.Supports verdict (SourceEntailment.Entails model (Domain sortDomain first) first.antecedent first.consequent)) :
    Guards.Supports verdict (SourceEntailment.Entails model (Domain sortDomain second) second.antecedent second.consequent) := by
  have equivalent := entails_iff model sortDomain renamed first second transport
  cases verdict with
  | yes => exact equivalent.mp sound
  | no => exact fun proved => sound (equivalent.mpr proved)
  | unknown => trivial

/-- A backend may additionally retain its verdict under these lossless query name changes. -/
def Stable (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) : Prop :=
  ∀ renamed first second, Transport model sortDomain renamed first second →
    solver first.declarations first.antecedent first.consequent =
      solver second.declarations second.antecedent second.consequent

/-- The exact solver query constructed by Entails and Satisfies after resolving scopes. -/
def ordinary (scopes : List Scope) (antecedent consequent : Formula) : Query :=
  ⟨SourceSortedQueries.declarations scopes,
    SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent),
    SourceGuards.applySubstitutions operations scopes consequent⟩

/-- All local domain and formula obligations follow from the actual source resolution stack. -/
theorem ordinary_agree (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceSemanticNames.ambient operations first guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv) :
    Agree model sortDomain (ordinary scopes antecedent consequent) (ordinary other antecedent consequent) firstEnv secondEnv :=
  ⟨SourceSortedQueries.domain_related sortDomain guard first second reads recipes scopes other resolved otherResolved firstEnv secondEnv related,
   antecedent_related model nullary laws guard first second reads recipes scopes other resolved otherResolved
     firstEnv secondEnv related antecedent leftNames,
   formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
     firstEnv secondEnv related consequent rightNames⟩

/-- Complete ordinary source queries meet the explicit backend transport contract. -/
theorem ordinary_transport (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceSemanticNames.ambient operations first guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard) :
    Transport model sortDomain (SourceFreshTables.tableRenaming operations guard first second)
      (ordinary scopes antecedent consequent) (ordinary other antecedent consequent) := by
  constructor
  · intro env
    exact ordinary_agree model nullary laws sortDomain guard first second reads recipes scopes other resolved otherResolved
      antecedent consequent leftNames rightNames _ env (forward_related model guard first second env)
  · intro env
    have unique := SourceFreshTables.renaming_unique operations guard first second
    exact ordinary_agree model nullary laws sortDomain guard first second reads recipes scopes other resolved otherResolved
      antecedent consequent leftNames rightNames env _
      (SourceScopeEnvironment.lift_related model _ _ unique.1 unique.2
        (SourceSemanticNames.live_avoid operations guard first second reads) env)

/-- The exact solver query constructed by Holds, including its positional declarations. -/
def contract (scopes : List Scope) (targets : List SourceGuards.Path)
    (values : List (SourceGuards.Observed Formula)) (consequent : Formula) : Query :=
  ⟨(((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) ++
      scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups,
    SourceGuards.withActualAssumptions operations scopes
      (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2),
    SourceGuards.applySubstitutions operations scopes consequent⟩

/-- Holds transports every positional alias, actual assumption, declaration, and nested scope. -/
theorem contract_agree (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (targets : List SourceGuards.Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values otherValues : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany first targets = some values) (otherFound : SourceGuards.observeMany second targets = some otherValues)
    (consequent : Formula) (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceContractNames.live guard first targets.length) firstEnv secondEnv) :
    Agree model sortDomain (contract scopes targets values consequent) (contract other targets otherValues consequent) firstEnv secondEnv := by
  refine ⟨?_, SourceHoldsQueries.antecedent_related model nullary laws guard first second reads recipes scopes other
    resolved otherResolved targets requested values otherValues found otherFound firstEnv secondEnv related,
    formula_related model nullary guard first second reads recipes scopes other resolved otherResolved firstEnv secondEnv
      (fun name member => related name (List.mem_append_left _ member)) consequent rightNames⟩
  exact (SourceHoldsQueries.domain_exact sortDomain targets.length scopes firstEnv).symm.trans
    ((SourceHoldsQueries.domain_related sortDomain guard first second reads recipes scopes other resolved otherResolved
      targets.length firstEnv secondEnv related).trans (SourceHoldsQueries.domain_exact sortDomain targets.length other secondEnv))

/-- Complete source Holds queries meet the same backend contract with constructed environments. -/
theorem contract_transport (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (targets : List SourceGuards.Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values otherValues : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany first targets = some values) (otherFound : SourceGuards.observeMany second targets = some otherValues)
    (consequent : Formula) (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard) :
    Transport model sortDomain (SourceFreshTables.tableRenaming operations guard first second)
      (contract scopes targets values consequent) (contract other targets otherValues consequent) := by
  constructor
  · intro env
    apply contract_agree model nullary laws sortDomain guard first second reads recipes scopes other resolved otherResolved
      targets requested values otherValues found otherFound consequent rightNames _ env
    intro name _
    exact FreshEnvironment.environment_names model env _ (SourceFreshTables.renaming_unique operations guard first second).1 name
  · intro env
    exact contract_agree model nullary laws sortDomain guard first second reads recipes scopes other resolved otherResolved
      targets requested values otherValues found otherFound consequent rightNames env _
      (SourceContractNames.lift_related model guard first second reads targets.length env)

end MicroCFTA.SourceQueryTransport
