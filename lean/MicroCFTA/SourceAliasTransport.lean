import MicroCFTA.GuardAlphaBoundary

/-!
# Transport the source safeguard through actual-value identification

Soundness suffices for positive mathematical entailment after identification.
Known identities also need environment lifting for a refutation. Exact
Yes/No/Unknown equality needs an additional solver stability contract.
-/
namespace MicroCFTA.SourceAliasTransport
open FullSyntax SourceFormula SourceEntailment

/-- Relevant original query environments lift through a simultaneous name replacement. -/
def Lifts (model : Interpretation Value) (source target : (Name → Value) → Prop)
    (renamed : List (Name × Name)) (antecedent consequent : Formula) : Prop :=
  ∀ original, source original → ∃ env, target env ∧
    FormulaSemantics.Agree (formulaNames antecedent ++ formulaNames consequent)
      (renamedEnvironment model env renamed) original

/-- Source No-to-Unknown weakening makes identification sound under the exact local environment obligations. -/
theorem decideWith_alias_sound (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value)
    (admitted : List (Name × Name) → (Name → Value) → Prop)
    (solver : SourceGuards.Entailment Formula) (sound : Sound model admitted solver)
    (bindings : List (Name × Name)) (scopes : List (List (SourceGuards.Resolved Formula)))
    (target : (Name → Value) → Prop) (renamed : List (Name × Name)) (antecedent consequent : Formula)
    (domains : ∀ env, target env →
      admitted (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups
        (renamedEnvironment model env renamed))
    (knownLifts : scopes.all (fun scope => scope.all SourceGuards.Resolved.identityKnown) = true →
      Lifts model (admitted (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups)
        target renamed antecedent consequent) :
    Guards.Supports (SourceGuards.decideWith solver bindings scopes antecedent consequent)
      (Entails model target (substitute renamed antecedent) (substitute renamed consequent)) := by
  have certified := sound (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups
    antecedent consequent
  cases answer : solver (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups
      antecedent consequent with
  | yes =>
      have yes : Entails model
          (admitted (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups)
          antecedent consequent := by simpa only [answer, Guards.Supports] using certified
      simp only [SourceGuards.decideWith, answer, Guards.Supports]
      exact rename_yes model nullary _ target renamed antecedent consequent domains yes
  | unknown => simp only [SourceGuards.decideWith, answer, Guards.Supports]
  | no =>
      by_cases known : scopes.all (fun scope => scope.all SourceGuards.Resolved.identityKnown) = true
      · have no : ¬Entails model
            (admitted (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups)
            antecedent consequent := by simpa only [answer, Guards.Supports] using certified
        simp only [SourceGuards.decideWith, answer, known, ↓reduceIte, Guards.Supports]
        intro proposed
        exact no ((rename_iff model nullary _ target renamed antecedent consequent domains (knownLifts known)).mp proposed)
      · simp only [SourceGuards.decideWith, answer, known, Bool.false_eq_true, ↓reduceIte, Guards.Supports]

/-- A solver can additionally preserve its whole verdict under lossless, domain-preserving name changes. -/
def RenamingStable (model : Interpretation Value)
    (admitted : List (Name × Name) → (Name → Value) → Prop)
    (solver : SourceGuards.Entailment Formula) : Prop :=
  ∀ bindings otherBindings renamed antecedent consequent,
    (∀ env, admitted otherBindings env → admitted bindings (renamedEnvironment model env renamed)) →
    Lifts model (admitted bindings) (admitted otherBindings) renamed antecedent consequent →
    solver otherBindings (substitute renamed antecedent) (substitute renamed consequent) =
      solver bindings antecedent consequent

/-- Under that extra contract, known-identity source queries preserve their exact verdict after renaming. -/
theorem known_renaming_exact (model : Interpretation Value)
    (admitted : List (Name × Name) → (Name → Value) → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : RenamingStable model admitted solver)
    (bindings : List (Name × Name)) (scopes : List (List (SourceGuards.Resolved Formula)))
    (otherBindings : List (Name × Name)) (renamed : List (Name × Name)) (antecedent consequent : Formula)
    (known : scopes.all (fun scope => scope.all SourceGuards.Resolved.identityKnown) = true)
    (domains : ∀ env, admitted otherBindings env →
      admitted (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups
        (renamedEnvironment model env renamed))
    (lifts : Lifts model (admitted (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups)
      (admitted otherBindings) renamed antecedent consequent) :
    SourceGuards.decideWith solver bindings scopes antecedent consequent =
      solver otherBindings (substitute renamed antecedent) (substitute renamed consequent) := by
  rw [SourceGuards.known_query solver bindings scopes antecedent consequent known]
  exact (stable _ otherBindings renamed antecedent consequent domains lifts).symm

end MicroCFTA.SourceAliasTransport
