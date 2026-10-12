import MicroCFTA.CurrentGuardPrune
import MicroCFTA.SourceCurrentReadBridge
import MicroCFTA.SourceCompleteLogical
import MicroCFTA.BooleanGuardCompile

/-!
# Logical safety of current evaluator-first pruning

The source retains a Yes candidate even when its actual table is ambiguous.
The quotient theorem proves complete logical satisfaction for those terms.
An ambiguous Unknown restores the original guarded edge, whose complete
certificates are sound. Exact backend Yes preservation is not required.
The planned-read bridge still uses its lossless spelling contract.
-/
namespace MicroCFTA.CurrentGuardLogicalPrune
open FullSyntax SourceFormula SourceGuards SourceObservations FullGuardPrune

/-- Every term in a current Yes variant satisfies the complete logical guard. -/
theorem variant_yes (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (variant : ObservationGraph.Variant State String Formula)
    (term : Language.Term (Observation.Label String Formula))
    (view : variant.view = Observation.signature (SourceGuardPlan.plan guard) term)
    (sound : ∀ context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain (sourceTerm term) context) solver)
    (yes : CurrentGuardPrune.variantVerdict operations solver guard variant = .yes) :
    SourceQuotientGuards.Public model sortDomain (sourceTerm term) true guard :=
  SourceCurrentReadBridge.cell_yes model nullary laws sortDomain solver stable guard _ (sourceTerm term)
    (view ▸ signature_reads guard term) sound yes

/-- Successful current pruning returns only original terms that satisfy the logical guard. -/
theorem prune_sound (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (sound : ∀ term context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : CurrentGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula))
    (retained : PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term) :
    Language.Accepts automaton state term ∧ SourceQuotientGuards.Public model sortDomain (sourceTerm term) true guard := by
  rcases PruneCandidates.check_success_cases _ [] (CurrentGuardPrune.candidates operations solver automaton guard state)
      result success with restored | ⟨finished, _⟩
  · rw [restored] at retained
    obtain ⟨edge, member, accepted⟩ := retained
    have equal := List.mem_singleton.mp member
    subst edge
    have original := (ObservationGraph.guardedRoot_accepts_iff automaton state
      (fun term => decide (SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes)) term).mp accepted
    exact ⟨original.1, SourceCompleteLogical.public_yes model sortDomain solver (sourceTerm term)
      (sound (sourceTerm term)) true guard (of_decide_eq_true original.2)⟩
  · rw [finished] at retained
    obtain ⟨edge, member, accepted⟩ := retained
    have present : edge ∈ PruneSchedule.decided (CurrentGuardPrune.candidates operations solver automaton guard state) := by
      simpa only [List.nil_append] using member
    obtain ⟨candidate, candidateMember, yes, rfl⟩ := (PruneCandidates.decided_member _ edge).mp present
    obtain ⟨variant, variantMember, rfl⟩ := List.mem_map.mp candidateMember
    have precise := ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant variantMember term accepted
    exact ⟨precise.1, variant_yes model nullary laws sortDomain solver stable guard variant term precise.2
      (sound (sourceTerm term)) yes⟩

/-- Successful current compilation can retain only a logically valid planned-read cell. -/
theorem compile_retained (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (sound : ∀ context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same : Bool)
    (success : BooleanGuardCompile.decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok true) :
    SourceQuotientGuards.Public model sortDomain term true guard := by
  apply SourceCurrentReadBridge.cell_yes model nullary laws sortDomain solver stable guard cell term reads sound
  exact BooleanGuardCompile.classification _ semantic allYes allNo mixedLeaf equalities same true success

end MicroCFTA.CurrentGuardLogicalPrune
