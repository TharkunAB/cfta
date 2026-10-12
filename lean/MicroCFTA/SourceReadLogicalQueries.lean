import MicroCFTA.SourceReadLogicalDomains
import MicroCFTA.SourceKnownHoldsTransport

/-!
# Logical queries across planned reads and actual identification

The first map changes sparse fresh-name spelling without losing identities.
The second map identifies actuals in a complete term. Both maps come from the
executed source tables. Solver soundness supplies mathematical evidence;
the proof does not require a backend to repeat its verdict after either map.
-/
namespace MicroCFTA.SourceReadLogicalQueries
open FullSyntax SourceFormula FormulaSubstitution SourceObservations
open SourceQuotientEnvironment SourceQuotientQueries SourceReadLogicalDomains
open SourceGuards (Guard Observations Path)

/-- Record the exact cell, exact-root, and complete scope resolutions for one recipe stack. -/
structure Stack (term : Language.Term (Label Formula)) (guard : Guard Formula) (cell : Observations Formula)
    (recipes : List Recipe) (old middle complete : List Scope) : Prop where
  source : SourceScopeStack.Resolves guard cell recipes old
  observed : SourceScopeStack.Resolves guard (observe term) recipes middle
  sparse : Resolves term guard (sameShape operations (observe term) []) recipes middle
  full : Resolves term guard (sameTerm operations term []) recipes complete
  accepted : Accepted middle

/-- The initial three evaluation contexts all have empty source scope stacks. -/
theorem empty_stack (term : Language.Term (Label Formula)) (guard : Guard Formula) (cell : Observations Formula) :
    Stack term guard cell [] [] [] [] := ⟨.nil, .nil, .nil, .nil, by trivial⟩

/-- Planned-read agreement preserves every formula-relevant ambient name. -/
theorem names_used (term : Language.Term (Label Formula)) (guard : Guard Formula) (cell : Observations Formula)
    (reads : SourceReadAgreement.Reads guard cell (observe term)) (formula : Formula)
    (names : ∀ name ∈ formulaNames formula, name ∈ SourceSemanticNames.ambient operations cell guard) :
    ∀ name ∈ formulaNames formula, name ∈ SourceGuards.usedNames operations (observe term) guard := by
  intro name member
  apply SourceSemanticNames.ambient_used operations (observe term) guard
  rw [← SourceSemanticNames.ambient_reads operations guard cell (observe term) reads]
  exact names name member

/-- A cell No also forces known identities in the corresponding exact-root scope stack. -/
theorem middle_known (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (cell : Observations Formula) (reads : SourceReadAgreement.Reads guard cell (observe term))
    (recipes : List Recipe) (old middle complete : List Scope) (stack : Stack term guard cell recipes old middle complete)
    (bindings : List (Name × Name)) (antecedent consequent : Formula)
    (no : SourceGuards.decideWith solver bindings old antecedent consequent = .no) : SourceKnownQueryTransport.Known middle := by
  have known := SourceKnownQueryTransport.no_known solver bindings old antecedent consequent no
  have flags := SourceCurrentReadTransport.flags _ old middle
    (SourceScopeSymbols.aligned guard cell (observe term) reads recipes old middle stack.source stack.observed)
  exact flags.symm.trans known

/-- Ordinary query evidence survives both source maps with the full ambient domain retained. -/
theorem ordinary (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (cell : Observations Formula) (reads : SourceReadAgreement.Reads guard cell (observe term))
    (compatible : Compatible sortDomain guard cell (observe term))
    (sound : SourceEntailment.Sound model (Admitted sortDomain cell guard) solver)
    (recipes : List Recipe) (old middle complete : List Scope) (stack : Stack term guard cell recipes old middle complete)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceSemanticNames.ambient operations cell guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations cell guard) :
    Guards.Supports (SourceGuards.decideWith solver [] old
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent))
      (SourceQuotientGuards.Query model sortDomain term guard complete antecedent consequent) := by
  have first := SourceEntailment.decideWith_sound model (Admitted sortDomain cell guard) solver sound [] old
    (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
    (SourceGuards.applySubstitutions operations old consequent)
  have transported := supports model sortDomain guard cell (observe term) compatible
    (SourceQueryTransport.ordinary old antecedent consequent) (SourceQueryTransport.ordinary middle antecedent consequent)
    (SourceQueryTransport.ordinary_transport model nullary laws sortDomain guard cell (observe term) reads recipes old middle
      stack.source stack.observed antecedent consequent leftNames rightNames) _ first
  change Guards.Supports _ (SourceQuotientGuards.Query model sortDomain term guard middle antecedent consequent) at transported
  cases verdict : SourceGuards.decideWith solver [] old
      (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old antecedent))
      (SourceGuards.applySubstitutions operations old consequent) with
  | unknown => trivial
  | yes =>
      rw [verdict] at transported
      exact entails_yes model nullary laws sortDomain term guard recipes middle complete stack.sparse stack.full stack.accepted
        antecedent consequent (names_used term guard cell reads antecedent leftNames) (names_used term guard cell reads consequent rightNames) transported
  | no =>
      rw [verdict] at transported
      intro proved
      exact transported (SourceKnownQueryTransport.entails_backward model nullary laws sortDomain term guard recipes middle complete
        stack.sparse stack.full (middle_known solver term guard cell reads recipes old middle complete stack [] _ _ verdict)
        antecedent consequent (names_used term guard cell reads antecedent leftNames) (names_used term guard cell reads consequent rightNames) proved)

/-- Holds evidence transports every positional domain and alias through both source maps. -/
theorem holds (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (cell : Observations Formula) (reads : SourceReadAgreement.Reads guard cell (observe term))
    (compatible : Compatible sortDomain guard cell (observe term))
    (sound : SourceEntailment.Sound model (Admitted sortDomain cell guard) solver)
    (recipes : List Recipe) (old middle complete : List Scope) (stack : Stack term guard cell recipes old middle complete)
    (targets : List Path) (requested : ∀ path ∈ targets, path ∈ SourceGuards.paths guard)
    (values otherValues : List (SourceGuards.Observed Formula))
    (found : SourceGuards.observeMany cell targets = some values)
    (otherFound : SourceGuards.observeMany (observe term) targets = some otherValues)
    (consequent : Formula) (names : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations cell guard) :
    Guards.Supports (SourceGuards.decideWith solver
      ((SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName))) old
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent))
      (SourceEntailment.Entails model (SourceQuotientHolds.Domain sortDomain term guard targets.length complete)
        (SourceGuards.withActualAssumptions operations complete
          (SourceGuards.applySubstitutions operations complete (SourceGuards.contract operations targets otherValues).2))
        (SourceGuards.applySubstitutions operations complete consequent)) := by
  have bindings : (SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName)) =
      (List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName)) := by
    simp [SourceGuards.contract, List.map_map, Function.comp_def]
  rw [bindings]
  have first := SourceEntailment.decideWith_sound model (Admitted sortDomain cell guard) solver sound
    ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
    (SourceGuards.withActualAssumptions operations old
      (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
    (SourceGuards.applySubstitutions operations old consequent)
  have transported := supports model sortDomain guard cell (observe term) compatible
    (SourceQueryTransport.contract old targets values consequent) (SourceQueryTransport.contract middle targets otherValues consequent)
    (SourceQueryTransport.contract_transport model nullary laws sortDomain guard cell (observe term) reads recipes old middle
      stack.source stack.observed targets requested values otherValues found otherFound consequent names) _ first
  have domains (env : Name → Value) :
      SourceQuotientHolds.Domain sortDomain term guard targets.length middle env ↔
        Admitted sortDomain (observe term) guard (SourceQueryTransport.contract middle targets otherValues consequent).declarations env := by
    exact and_congr Iff.rfl (SourceHoldsQueries.domain_exact sortDomain targets.length middle env)
  have middleEvidence : Guards.Supports (SourceGuards.decideWith solver
      ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent))
      (SourceEntailment.Entails model (SourceQuotientHolds.Domain sortDomain term guard targets.length middle)
        (SourceGuards.withActualAssumptions operations middle
          (SourceGuards.applySubstitutions operations middle (SourceGuards.contract operations targets otherValues).2))
        (SourceGuards.applySubstitutions operations middle consequent)) := by
    cases verdict : SourceGuards.decideWith solver _ old _ _ with
    | unknown => trivial
    | yes =>
        rw [verdict] at transported
        intro env allowed assumed
        exact transported env ((domains env).mp allowed) assumed
    | no =>
        rw [verdict] at transported
        intro proved
        apply transported
        intro env allowed assumed
        exact proved env ((domains env).mpr allowed) assumed
  cases verdict : SourceGuards.decideWith solver
      ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) old
      (SourceGuards.withActualAssumptions operations old
        (SourceGuards.applySubstitutions operations old (SourceGuards.contract operations targets values).2))
      (SourceGuards.applySubstitutions operations old consequent) with
  | unknown => trivial
  | yes =>
      rw [verdict] at middleEvidence
      exact SourceQuotientHolds.entails_yes model nullary laws sortDomain term guard recipes middle complete stack.sparse stack.full
        stack.accepted targets requested otherValues otherFound consequent (names_used term guard cell reads consequent names) middleEvidence
  | no =>
      rw [verdict] at middleEvidence
      intro proved
      exact middleEvidence (SourceKnownHoldsTransport.entails_backward model nullary laws sortDomain term guard recipes middle complete
        stack.sparse stack.full (middle_known solver term guard cell reads recipes old middle complete stack _ _ _ verdict)
        targets requested otherValues otherFound consequent (names_used term guard cell reads consequent names) proved)

end MicroCFTA.SourceReadLogicalQueries
