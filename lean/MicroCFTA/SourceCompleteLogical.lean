import MicroCFTA.SourceQuotientGuards

/-!
# Complete source guard soundness

Complete evaluator certificates imply the same logical guard judgment used
by the quotient proof. This covers the original guarded edge on fallback.
No solver completeness or exact sparse verdict stability is required.
-/
namespace MicroCFTA.SourceCompleteLogical
open FullSyntax SourceFormula SourceObservations SourceQuotientEnvironment SourceQuotientQueries SourceQuotientGuards
open SourceGuards (Guard Resolved)

/-- Execute the current complete worker with its enclosing allocation table. -/
def evaluate (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (outer : Guard Formula) (scopes : List Scope) (positive : Bool) (inner : Guard Formula) : Guards.Verdict :=
  let table := SourceGuards.substitutionValues operations (observe term) (sameTerm operations term []) outer
  SourceSubstitutionPrecedence.evaluateWith operations solver (observe term) (sameTerm operations term)
    table.1 table.2 scopes positive inner

private theorem query_supports (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term outer) solver)
    (scopes : List Scope) (antecedent consequent : Formula) :
    Guards.Supports (SourceGuards.decideWith solver [] scopes
      (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
      (SourceGuards.applySubstitutions operations scopes consequent))
      (Query model sortDomain term outer scopes antecedent consequent) :=
  SourceEntailment.decideWith_sound model (SolverDomain sortDomain term outer) solver sound [] scopes _ _

private theorem absence (positive : Bool) (yes : SourceGuards.absent positive = .yes) : positive = false := by
  cases positive <;> simp_all [SourceGuards.absent]

/-- Every complete worker Yes is a mathematical certificate for the source polarity judgment. -/
theorem worker_yes (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term outer) solver)
    (scopes : List Scope) (positive : Bool) (inner : Guard Formula)
    (yes : evaluate solver term outer scopes positive inner = .yes) :
    Logical model sortDomain term outer scopes positive inner := by
  cases inner with
  | top | bottom => cases positive <;> simp_all [evaluate, SourceSubstitutionPrecedence.evaluateWith,
      SourceEnclosingRenames.evaluateWith, SourceGuards.polarize, Guards.negate, Logical]
  | same left right =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases leftFound : observe term left with
      | none => simpa only [leftFound] using absence positive (by simpa only [leftFound] using yes)
      | some a => cases rightFound : observe term right with
        | none => simpa only [leftFound, rightFound] using absence positive (by simpa only [leftFound, rightFound] using yes)
        | some b =>
            simp only [leftFound, rightFound] at yes ⊢
            by_cases equal : left = right
            · subst right
              have polarity : positive = true := by cases positive <;> simp_all [SourceGuards.polarize, Guards.negate]
              subst positive
              obtain ⟨subterm, present, _⟩ := Option.map_eq_some_iff.mp leftFound
              simp only [sameTerm, present, pure]
              exact congrArg some ((Language.termEq_correct _ _).mpr rfl)
            · simp only [equal, ↓reduceIte] at yes
              cases decided : sameTerm operations term scopes left right with
              | none => cases positive <;> simp_all [SourceGuards.polarize, Guards.negate]
              | some answer =>
                  have polarity : answer = positive := by cases positive <;> cases answer <;>
                    simp_all [SourceGuards.polarize, Guards.negate]
                  exact congrArg some polarity
  | entails left right =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases leftFound : observe term left with
      | none => simpa only [leftFound] using absence positive (by simpa only [leftFound] using yes)
      | some a => cases rightFound : observe term right with
        | none => simpa only [leftFound, rightFound] using absence positive (by simpa only [leftFound, rightFound] using yes)
        | some b =>
            simp only [leftFound, rightFound] at yes ⊢
            have support := query_supports model sortDomain solver term outer sound scopes a.refinement b.refinement
            cases positive <;> cases result : SourceGuards.decideWith solver [] scopes
                (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes a.refinement))
                (SourceGuards.applySubstitutions operations scopes b.refinement) <;>
              simp_all [SourceGuards.polarize, Guards.negate, Guards.Supports]
  | satisfies target requirement =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases found : observe term target with
      | none => simpa only [found] using absence positive (by simpa only [found] using yes)
      | some value =>
          simp only [found] at yes ⊢
          have support := query_supports model sortDomain solver term outer sound scopes value.refinement
            (if positive then requirement else operations.negate requirement)
          simpa only [yes, Guards.Supports] using support
  | holds targets requirement =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases found : SourceGuards.observeMany (observe term) targets with
      | none => simpa only [found] using absence positive (by simpa only [found] using yes)
      | some values =>
          simp only [found] at yes ⊢
          have bindings : (SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName)) =
              (List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName)) := by
            simp [SourceGuards.contract, List.map_map, Function.comp_def]
          rw [bindings] at yes
          have support := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term outer) solver sound
            ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) scopes
            (SourceGuards.withActualAssumptions operations scopes
              (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2))
            (SourceGuards.applySubstitutions operations scopes (if positive then requirement else operations.negate requirement))
          rw [yes] at support
          intro env allowed assumed
          exact support env ⟨allowed.1, (SourceHoldsQueries.domain_exact sortDomain targets.length scopes env).mp allowed.2⟩ assumed
  | substitute additions inner =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases found : resolve term outer (sameTerm operations term []) additions with
      | none =>
          have rawFound := found
          unfold resolve at rawFound
          simpa only [] using absence positive (by simpa only [rawFound] using yes)
      | some scope =>
          have rawFound := found
          unfold resolve at rawFound
          simp only [rawFound] at yes
          split at yes
          · contradiction
          · exact worker_yes model sortDomain solver term outer sound (scope :: scopes) positive inner yes
  | not inner =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      exact worker_yes model sortDomain solver term outer sound scopes (!positive) inner yes
  | and parts | or parts =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      change SourceGuards.combine _ (parts.map (evaluate solver term outer scopes positive)) = .yes at yes
      simp only [Logical]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals first
        | (intro part member
           apply worker_yes model sortDomain solver term outer sound scopes _ part
           exact (GuardConjunction.combine_yes _).mp yes _ (List.mem_map.mpr ⟨part, member, rfl⟩))
        | (obtain ⟨part, member, proved⟩ := List.mem_map.mp ((GuardConjunction.disjoin_yes _).mp yes)
           exact ⟨⟨part, member⟩, worker_yes model sortDomain solver term outer sound scopes _ part proved⟩)
termination_by sizeOf inner

/-- The complete public evaluator confirms only logically valid guards. -/
theorem public_yes (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (sound : ∀ guard, SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (positive : Bool) (guard : Guard Formula)
    (yes : SourceSubstitutionPrecedence.evaluate operations solver (observe term) (sameTerm operations term) positive guard = .yes) :
    Public model sortDomain term positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceSubstitutionPrecedence.evaluate] at yes
      simp only [Public]
      exact worker_yes model sortDomain solver term _ (sound _) [] positive _ yes
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceSubstitutionPrecedence.evaluate] at yes
          simp only [Public]
          exact public_yes model sortDomain solver term sound positive inner yes
      | cons first rest =>
          simp only [SourceSubstitutionPrecedence.evaluate] at yes
          simp only [Public]
          exact worker_yes model sortDomain solver term _ (sound _) [] positive _ yes
  | not inner =>
      simp only [SourceSubstitutionPrecedence.evaluate] at yes
      simp only [Public]
      exact public_yes model sortDomain solver term sound (!positive) inner yes
  | and parts | or parts =>
      simp only [SourceSubstitutionPrecedence.evaluate] at yes
      simp only [Public]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals first
        | (intro part member
           apply public_yes model sortDomain solver term sound _ part
           exact (GuardConjunction.combine_yes _).mp yes _ (List.mem_map.mpr ⟨part, member, rfl⟩))
        | (obtain ⟨part, member, proved⟩ := List.mem_map.mp ((GuardConjunction.disjoin_yes _).mp yes)
           exact ⟨⟨part, member⟩, public_yes model sortDomain solver term sound _ part proved⟩)
termination_by sizeOf guard

end MicroCFTA.SourceCompleteLogical
