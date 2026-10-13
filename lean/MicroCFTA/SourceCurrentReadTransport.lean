import MicroCFTA.SourceQuotientGuards

/-!
# Current source decisions under lossless read transport

Planned reads can change irrelevant constructor names in the avoid list.
The existing lossless fresh-name transport applies to ambiguous tables too.
Identity flags and both scope checks remain equal under that transport.
Exact verdict equality here uses the explicit backend spelling contract.
-/
namespace MicroCFTA.SourceCurrentReadTransport
open FullSyntax SourceFormula SourceScopeStack

/-- Corresponding resolved records keep the runtime identity-known flags. -/
theorem flags (renamed : List (Name × Name)) (first second : List Scope)
    (paired : Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned renamed)) first second) :
    first.all (fun scope => scope.all SourceGuards.Resolved.identityKnown) =
      second.all (fun scope => scope.all SourceGuards.Resolved.identityKnown) := by
  induction paired with
  | nil => rfl
  | @cons first second rest other head tail ih =>
      have rows : first.all SourceGuards.Resolved.identityKnown = second.all SourceGuards.Resolved.identityKnown := by
        induction head with
        | nil => rfl
        | cons row rows ih => simp [row.2.2.2, ih]
      simp only [List.all_cons, rows, ih]

/-- Equal solver answers and equal identity flags give the same runtime decision. -/
theorem decision_equal (solver : SourceGuards.Entailment Formula) (bindings otherBindings : List (Name × Name))
    (scopes other : List Scope) (antecedent consequent otherAntecedent otherConsequent : Formula)
    (known : scopes.all (fun scope => scope.all SourceGuards.Resolved.identityKnown) =
      other.all (fun scope => scope.all SourceGuards.Resolved.identityKnown))
    (answer : solver (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups antecedent consequent =
      solver (otherBindings ++ other.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups otherAntecedent otherConsequent) :
    SourceGuards.decideWith solver bindings scopes antecedent consequent =
      SourceGuards.decideWith solver otherBindings other otherAntecedent otherConsequent := by
  simp only [SourceGuards.decideWith, answer, known]

/-- Entails and Satisfies retain their exact decisions when the backend preserves the constructed transport. -/
theorem ordinary (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second)
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
  apply decision_equal solver [] [] scopes other _ _ _ _
    (flags _ _ _ (SourceScopeSymbols.aligned guard first second reads recipes scopes other resolved otherResolved))
  exact stable _ _ _ (SourceQueryTransport.ordinary_transport model nullary laws sortDomain guard first second reads
    recipes scopes other resolved otherResolved antecedent consequent leftNames rightNames)

/-- Holds retains its exact decision under the same contract, including positional declarations. -/
theorem holds (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second)
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
  apply decision_equal solver _ _ scopes other _ _ _ _
    (flags _ _ _ (SourceScopeSymbols.aligned guard first second reads recipes scopes other resolved otherResolved))
  have exact := stable _ _ _ (SourceQueryTransport.contract_transport model nullary laws sortDomain guard first second reads
    recipes scopes other resolved otherResolved targets requested values otherValues found otherFound consequent rightNames)
  simpa only [SourceGuards.contract, SourceQueryTransport.contract, List.map_map, Function.comp_def] using exact

/-- Any test of literal symbols and identity flags ignores fresh spelling changes. -/
theorem any_metadata (renamed : List (Name × Name)) (first second : Scope)
    (paired : Language.All₂ (SourceResolvedTables.Aligned renamed) first second)
    (test : (Name × Name) → Bool → Bool) :
    first.any (fun row => test row.symbolReplacement row.identityKnown) =
      second.any (fun row => test row.symbolReplacement row.identityKnown) := by
  induction paired with
  | nil => rfl
  | cons head tail ih => simp only [List.any_cons, head.2.1, head.2.2.2, ih]

/-- The identity-precedence safeguard ignores fresh spelling changes. -/
theorem precedence (renamed : List (Name × Name)) (first second : Scope)
    (paired : Language.All₂ (SourceResolvedTables.Aligned renamed) first second) :
    SourceSubstitutionPrecedence.ambiguousIdentityPrecedence first =
      SourceSubstitutionPrecedence.ambiguousIdentityPrecedence second := by
  induction paired with
  | nil => rfl
  | @cons first second rest other head tail ih =>
      have same := any_metadata renamed rest other tail (fun symbol _ =>
        decide (symbol.1 = first.symbolReplacement.1) && decide (symbol.2 ≠ symbol.1))
      simp only [SourceSubstitutionPrecedence.ambiguousIdentityPrecedence, head.2.1, head.2.2.2, ih, same]

/-- Enclosing literal formal names stay identical under the lossless table map. -/
theorem enclosing (renamed : List (Name × Name)) (first second : List Scope)
    (paired : Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned renamed)) first second) :
    SourceEnclosingRenames.enclosingFormals first = SourceEnclosingRenames.enclosingFormals second := by
  induction paired with
  | nil => rfl
  | @cons first second rest other head tail ih =>
      have symbols := SourceScopeSymbols.replacements renamed first second head
      have names := congrArg (List.map Prod.fst) symbols
      simp only [List.map_map, Function.comp_def] at names
      simp only [SourceEnclosingRenames.enclosingFormals, List.flatMap_cons] at *
      rw [names, ih]

/-- Both source scope-entry checks commute with the read-table name map. -/
theorem checks (renamed : List (Name × Name)) (scope otherScope : Scope) (first second : List Scope)
    (head : Language.All₂ (SourceResolvedTables.Aligned renamed) scope otherScope)
    (tail : Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned renamed)) first second) :
    (scope.any (SourceEnclosingRenames.renamedByEnclosing first) || SourceSubstitutionPrecedence.ambiguousIdentityPrecedence scope) =
      (otherScope.any (SourceEnclosingRenames.renamedByEnclosing second) || SourceSubstitutionPrecedence.ambiguousIdentityPrecedence otherScope) := by
  have renamed := any_metadata renamed scope otherScope head
    (fun symbol known => !known && (SourceEnclosingRenames.enclosingFormals second).contains symbol.2)
  have expand (scopes : List Scope) : SourceEnclosingRenames.renamedByEnclosing scopes =
      (fun row : SourceGuards.Resolved Formula => !row.identityKnown &&
        (SourceEnclosingRenames.enclosingFormals scopes).contains row.symbolReplacement.2) := by
    funext row
    rfl
  rw [expand first, expand second]
  simp only [enclosing _ _ _ tail, renamed, precedence _ _ _ head]

end MicroCFTA.SourceCurrentReadTransport
