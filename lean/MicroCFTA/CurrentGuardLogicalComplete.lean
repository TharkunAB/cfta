import MicroCFTA.CurrentGuardLogicalPrune
import MicroCFTA.SourceQuotientRefutations

/-!
# Completeness of successful current pruning

A current sparse No excludes complete logical satisfaction. A finished
candidate pass therefore keeps every logical-valid original term. Unknown
fallback keeps the complete guarded edge, whose executable acceptance still
requires a complete backend Yes. We state that condition separately.
-/
namespace MicroCFTA.CurrentGuardLogicalComplete
open FullSyntax SourceFormula SourceGuards SourceObservations FullGuardPrune

/-- A current No cell excludes every represented term from the complete logical judgment. -/
theorem cell_no (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (sound : ∀ context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (no : SourceSubstitutionPrecedence.evaluateGuardWithShape operations solver cell guard = .no) :
    ¬SourceQuotientGuards.Public model sortDomain term true guard := by
  apply SourceQuotientRefutations.public_no model nullary laws sortDomain solver term sound true guard
  exact (SourceCurrentReadBridge.public_equal model nullary laws sortDomain solver stable guard cell (observe term) reads true).symm.trans no

/-- Candidate completion is logically complete; restoration uses the original executable guard. -/
theorem prune_contains (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (sound : ∀ term context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) (accepted : Language.Accepts automaton state term)
    (logical : SourceQuotientGuards.Public model sortDomain (sourceTerm term) true guard)
    (restoredYes : result = [ObservationGraph.guardedRoot automaton state
      (fun term => decide (SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes))] →
      SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term := by
  rcases PruneCandidates.check_success_cases _ [] (CurrentGuardPrune.candidates operations solver automaton guard state)
      result success with restored | ⟨finished, complete⟩
  · rw [restored]
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    apply (ObservationGraph.guardedRoot_accepts_iff automaton state _ term).mpr
    exact ⟨accepted, decide_eq_true (restoredYes restored)⟩
  · obtain ⟨variant, present, run⟩ := (ObservationGraph.specialize_cover automaton
        (ObservationGraph.planBudget (SourceGuardPlan.plan guard)) (SourceGuardPlan.plan guard) state term).mpr accepted
    let candidate : PruneSchedule.Candidate (ObservationGraph.Node State (Observation.Label String Formula)) :=
      ⟨variant.node, CurrentGuardPrune.variantVerdict operations solver guard variant,
        !(ambiguous (queryObservations variant.view) (fun _ _ => none) guard).isEmpty⟩
    have member : candidate ∈ CurrentGuardPrune.candidates operations solver automaton guard state :=
      List.mem_map.mpr ⟨variant, present, rfl⟩
    cases verdict : candidate.verdict with
    | unknown => exact False.elim (complete candidate member verdict)
    | no =>
        have view := (ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant present term run).2
        exact False.elim (cell_no model nullary laws sortDomain solver stable guard _ (sourceTerm term)
          (view ▸ signature_reads guard term) (sound (sourceTerm term)) verdict logical)
    | yes =>
        rw [finished]
        exact ⟨candidate.edge, by simpa only [List.nil_append] using
          (PruneCandidates.decided_member _ candidate.edge).mpr ⟨candidate, member, verdict, rfl⟩, run⟩

/-- Successful pruning never removes an original term with a complete backend Yes. -/
theorem confirmed_retained (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (sound : ∀ term context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) (accepted : Language.Accepts automaton state term)
    (yes : SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term :=
  prune_contains model nullary laws sortDomain solver stable automaton guard state sound result success term accepted
    (SourceCompleteLogical.public_yes model sortDomain solver (sourceTerm term) (sound (sourceTerm term)) true guard yes)
    (fun _ => yes)

/-- Logical completeness on the original edge is the exact additional fallback obligation. -/
def FallbackAdequate (model : Interpretation Value) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (automaton : Language.Automaton State (Observation.Label String Formula))
    (guard : Guard Formula) (state : State) : Prop :=
  ∀ term, Language.Accepts automaton state term → SourceQuotientGuards.Public model sortDomain (sourceTerm term) true guard →
    SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes

/-- Under explicit fallback adequacy, every successful current result equals the complete logical language. -/
theorem prune_exact_logical (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (sound : ∀ term context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (adequate : FallbackAdequate model sortDomain solver automaton guard state)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term ↔
      Language.Accepts automaton state term ∧ SourceQuotientGuards.Public model sortDomain (sourceTerm term) true guard := by
  constructor
  · exact CurrentGuardLogicalPrune.prune_sound model nullary laws sortDomain solver stable automaton guard state sound result success term
  · rintro ⟨accepted, logical⟩
    exact prune_contains model nullary laws sortDomain solver stable automaton guard state sound result success term accepted logical
      (fun _ => adequate term accepted logical)

/-- Successful compiler exclusion refutes every complete logical term in its planned-read cell. -/
theorem compile_excluded (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (sound : ∀ context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same : Bool)
    (success : BooleanGuardCompile.decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok false) :
    ¬SourceQuotientGuards.Public model sortDomain term true guard := by
  apply cell_no model nullary laws sortDomain solver stable guard cell term reads sound
  exact BooleanGuardCompile.classification _ semantic allYes allNo mixedLeaf equalities same false success

/-- A successful compiler decision equals complete logical validity for every represented term. -/
theorem compile_exact_logical (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (sound : ∀ context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same answer : Bool)
    (success : BooleanGuardCompile.decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    answer = true ↔ SourceQuotientGuards.Public model sortDomain term true guard := by
  cases answer with
  | true => exact ⟨fun _ => CurrentGuardLogicalPrune.compile_retained model nullary laws sortDomain solver stable guard cell term reads sound
      semantic allYes allNo mixedLeaf equalities same success, fun _ => rfl⟩
  | false => exact ⟨fun impossible => Bool.noConfusion impossible,
      fun logical => False.elim (compile_excluded model nullary laws sortDomain solver stable guard cell term reads sound
        semantic allYes allNo mixedLeaf equalities same success logical)⟩

end MicroCFTA.CurrentGuardLogicalComplete
