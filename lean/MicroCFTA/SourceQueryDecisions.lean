import MicroCFTA.SourceKnownScopes

/-!
# Exact source decisions under an explicit backend contract

The ambiguity gate supplies known flags. Concrete source query transport
supplies the backend contract premises. No query-equality premise is assumed.
-/
namespace MicroCFTA.SourceQueryDecisions
open FullSyntax SourceFormula SourceScopeStack

/-- Entails and Satisfies retain their exact decisions when the backend preserves the constructed transport. -/
theorem ordinary (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second)
    (unambiguous : SourceGuards.ambiguous first (SourceObservations.sameShape operations first []) guard = [])
    (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceSemanticNames.ambient operations first guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard) :
    SourceGuards.decideWith solver [] scopes
      (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
      (SourceGuards.applySubstitutions operations scopes consequent) =
    SourceGuards.decideWith solver [] other
      (SourceGuards.withActualAssumptions operations other (SourceGuards.applySubstitutions operations other antecedent))
      (SourceGuards.applySubstitutions operations other consequent) := by
  rw [SourceGuards.known_query solver [] scopes _ _ (SourceKnownScopes.scopes_known guard first unambiguous recipes scopes resolved),
    SourceGuards.known_query solver [] other _ _ (SourceKnownScopes.scopes_known guard second
      (SourceKnownScopes.reads_known guard first second reads unambiguous) recipes other otherResolved)]
  exact stable _ _ _ (SourceQueryTransport.ordinary_transport model nullary laws sortDomain guard first second reads
    recipes scopes other resolved otherResolved antecedent consequent leftNames rightNames)

/-- Holds retains its exact decision under the same contract, including positional declarations. -/
theorem holds (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second)
    (unambiguous : SourceGuards.ambiguous first (SourceObservations.sameShape operations first []) guard = [])
    (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (targets : List SourceGuards.Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values otherValues : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany first targets = some values) (otherFound : SourceGuards.observeMany second targets = some otherValues)
    (consequent : Formula) (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard) :
    SourceGuards.decideWith solver ((SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName))) scopes
      (SourceGuards.withActualAssumptions operations scopes
        (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations scopes consequent) =
    SourceGuards.decideWith solver ((SourceGuards.contract operations targets otherValues).1.map (fun name => (name, SourceGuards.valueName))) other
      (SourceGuards.withActualAssumptions operations other
        (SourceGuards.applySubstitutions operations other (SourceGuards.contract operations targets otherValues).2))
      (SourceGuards.applySubstitutions operations other consequent) := by
  rw [SourceGuards.known_query solver _ scopes _ _ (SourceKnownScopes.scopes_known guard first unambiguous recipes scopes resolved),
    SourceGuards.known_query solver _ other _ _ (SourceKnownScopes.scopes_known guard second
      (SourceKnownScopes.reads_known guard first second reads unambiguous) recipes other otherResolved)]
  have exact := stable _ _ _ (SourceQueryTransport.contract_transport model nullary laws sortDomain guard first second reads
    recipes scopes other resolved otherResolved targets requested values otherValues found otherFound consequent rightNames)
  simpa only [SourceGuards.contract, SourceQueryTransport.contract, List.map_map, Function.comp_def] using exact

end MicroCFTA.SourceQueryDecisions
