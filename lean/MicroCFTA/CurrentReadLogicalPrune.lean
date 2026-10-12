import MicroCFTA.CurrentGuardLogicalComplete
import MicroCFTA.SourceReadLogicalGuards

/-!
# Pruning and compilation over unrestricted ambient values without verdict stability

The repaired source evaluator supplies logical evidence through planned
reads and actual identity quotients. Only solver soundness is required.
An original-edge fallback retains its executable backend-Yes condition.
-/
namespace MicroCFTA.CurrentReadLogicalPrune
open FullSyntax SourceFormula SourceGuards SourceObservations FullGuardPrune

/-- The complete guard judgment retains formula sorts and unrestricted ambient values. -/
abbrev Logical (model : Interpretation Value) (term : Language.Term (Label Formula)) (guard : Guard Formula) : Prop :=
  SourceQuotientGuards.Public model (fun _ _ => True) term true guard

/-- The actual planned cell supplies both positive and negative logical evidence. -/
theorem cell_supports (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (solver : Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term)) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluateGuardWithShape operations solver cell guard) (Logical model term guard) := by
  apply SourceReadLogicalGuards.public_supports model nullary laws (fun _ _ => True) solver term guard cell reads
    (fun _ _ => ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩) _ true
  intro context _ declarations antecedent consequent
  have evidence := sound declarations antecedent consequent
  simpa [SourceEntailment.Entails, SourceReadLogicalDomains.Admitted, SourceReadLogicalDomains.Ambient] using evidence

/-- The fallback edge's complete backend certificate has the same logical meaning. -/
theorem complete_yes (model : Interpretation Value) (solver : Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (guard : Guard Formula) (term : Language.Term (Label Formula))
    (yes : SourceSubstitutionPrecedence.evaluateGuard operations solver guard term = .yes) : Logical model term guard := by
  apply SourceCompleteLogical.public_yes model (fun _ _ => True) solver term _ true guard yes
  intro context declarations antecedent consequent
  have evidence := sound declarations antecedent consequent
  simpa [SourceEntailment.Entails, SourceQuotientQueries.SolverDomain, SourceQuotientQueries.AmbientDomain] using evidence

/-- A successful prune returns only original, logically valid terms. -/
theorem prune_sound (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (solver : Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula))
    (retained : PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term) :
    Language.Accepts automaton state term ∧ Logical model (sourceTerm term) guard := by
  rcases PruneCandidates.check_success_cases _ [] (CurrentGuardPrune.candidates operations solver automaton guard state)
      result success with restored | ⟨finished, _⟩
  · rw [restored] at retained
    obtain ⟨edge, member, accepted⟩ := retained
    have equal := List.mem_singleton.mp member
    subst edge
    have original := (ObservationGraph.guardedRoot_accepts_iff automaton state
      (fun term => decide (SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes)) term).mp accepted
    exact ⟨original.1, complete_yes model solver sound guard (sourceTerm term) (of_decide_eq_true original.2)⟩
  · rw [finished] at retained
    obtain ⟨edge, member, accepted⟩ := retained
    have present : edge ∈ PruneSchedule.decided (CurrentGuardPrune.candidates operations solver automaton guard state) := by
      simpa only [List.nil_append] using member
    obtain ⟨candidate, candidateMember, yes, rfl⟩ := (PruneCandidates.decided_member _ edge).mp present
    obtain ⟨variant, variantMember, rfl⟩ := List.mem_map.mp candidateMember
    have precise := ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant variantMember term accepted
    have evidence := cell_supports model nullary laws solver sound guard (queryObservations variant.view) (sourceTerm term)
      (precise.2 ▸ signature_reads guard term)
    have decided : SourceSubstitutionPrecedence.evaluateGuardWithShape operations solver
        (queryObservations variant.view) guard = .yes := yes
    rw [decided] at evidence
    exact ⟨precise.1, evidence⟩

/-- Logical completeness needs a backend Yes only if the original edge is restored. -/
theorem prune_contains (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (solver : Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) (accepted : Language.Accepts automaton state term)
    (logical : Logical model (sourceTerm term) guard)
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
        have evidence := cell_supports model nullary laws solver sound guard (queryObservations variant.view) (sourceTerm term)
          (view ▸ signature_reads guard term)
        have refuted : ¬Logical model (sourceTerm term) guard := by
          change Guards.Supports candidate.verdict _ at evidence
          simpa only [verdict, Guards.Supports] using evidence
        exact False.elim (refuted logical)
    | yes =>
        rw [finished]
        exact ⟨candidate.edge, by simpa only [List.nil_append] using
          (PruneCandidates.decided_member _ candidate.edge).mpr ⟨candidate, member, verdict, rfl⟩, run⟩

/-- Every original backend-confirmed term survives successful pruning. -/
theorem confirmed_retained (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (solver : Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) (accepted : Language.Accepts automaton state term)
    (yes : SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term :=
  prune_contains model nullary laws solver sound automaton guard state result success term accepted
    (complete_yes model solver sound guard (sourceTerm term) yes) (fun _ => yes)

/-- Logical equality uses backend adequacy only for original-edge restoration. -/
theorem prune_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (solver : Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (adequate : result = [ObservationGraph.guardedRoot automaton state
      (fun term => decide (SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes))] →
      ∀ term, Language.Accepts automaton state term → Logical model (sourceTerm term) guard →
        SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes)
    (term : Language.Term (Observation.Label String Formula)) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term ↔
      Language.Accepts automaton state term ∧ Logical model (sourceTerm term) guard := by
  constructor
  · exact prune_sound model nullary laws solver sound automaton guard state result success term
  · rintro ⟨accepted, logical⟩
    exact prune_contains model nullary laws solver sound automaton guard state result success term accepted logical
      (fun restored => adequate restored term accepted logical)

/-- Successful compiler classification equals complete logical validity. -/
theorem compile_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (solver : Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same answer : Bool)
    (success : BooleanGuardCompile.decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    answer = true ↔ Logical model term guard := by
  have evidence := cell_supports model nullary laws solver sound guard cell term reads
  have classified := BooleanGuardCompile.classification _ semantic allYes allNo mixedLeaf equalities same answer success
  cases answer <;> simp_all [Guards.Supports]

end MicroCFTA.CurrentReadLogicalPrune
