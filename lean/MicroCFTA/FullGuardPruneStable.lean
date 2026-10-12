import MicroCFTA.SourceFullGuardBridge

/-!
# Full guarded candidate pruning with allocated identity conflicts

The repaired ambiguity gate and exact source query transport remove the old
conflict-free restriction. Exact confirmed-language preservation still needs
the stated backend name-transport contract.
-/
namespace MicroCFTA.FullGuardPruneStable
open FullSyntax SourceFormula SourceGuards SourceObservations FullGuardPrune

/-- The source conservative gate includes every identity unresolved by sparse root comparison. -/
theorem gate_unambiguous (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula)
    (gate : ambiguous observed (fun _ _ => none) guard = []) :
    ambiguous observed (sameShape formulas observed []) guard = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro path member
  obtain ⟨actual, present, target, other, otherPresent, different, name, refinement, _, shapes⟩ :=
    (SourceActuals.ambiguous_iff observed (sameShape formulas observed []) guard path).mp member
  have forbidden := (SourceActuals.ambiguous_iff observed (fun _ _ => none) guard path).mpr
    ⟨actual, present, target, other, otherPresent, different, name, refinement, rfl, shapes⟩
  simp [gate] at forbidden

/-- Every decided safe variant agrees with complete evaluation of its represented terms. -/
theorem variant_decided (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (variant : ObservationGraph.Variant State String Formula)
    (term : Language.Term (Observation.Label String Formula))
    (view : variant.view = Observation.signature (SourceGuardPlan.plan guard) term)
    (answer : Guards.Verdict) (decided : answer ≠ .unknown)
    (found : variantVerdict operations solver guard variant = answer) :
    evaluateGuard operations solver guard (sourceTerm term) = answer := by
  have gateClear : ambiguous (queryObservations variant.view) (fun _ _ => none) guard = [] := by
    unfold variantVerdict PruneSchedule.safeVerdict at found
    split at found
    · exact False.elim (decided found.symm)
    · rename_i empty
      simpa using empty
  have clear := gate_unambiguous operations (queryObservations variant.view) guard gateClear
  have raw : evaluateGuardWithShape operations solver (queryObservations variant.view) guard = answer := by
    simpa [variantVerdict, gateClear, PruneSchedule.safeVerdict] using found
  have reads : SourceReadAgreement.Reads guard (queryObservations variant.view) (observe (sourceTerm term)) :=
    view ▸ signature_reads guard term
  exact (SourceFullGuardBridge.complete_decision model nullary laws sortDomain solver stable guard _ (sourceTerm term) reads clear
    (fun unknown => decided (raw.symm.trans unknown))).symm.trans raw

/-- Every successful full-guard candidate pass preserves all confirmed terms, including fresh-name conflicts and ambiguity fallback. -/
theorem prune_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : FullGuardPrune.prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term ↔
      Language.Accepts automaton state term ∧ evaluateGuard operations solver guard (sourceTerm term) = .yes := by
  have exact := PruneCandidates.check_exact (ObservationGraph.AcceptsNode automaton)
    (fun candidate term => ObservationGraph.AcceptsNode automaton candidate.edge term ∧
      evaluateGuard operations solver guard (sourceTerm term) = .yes)
    (ObservationGraph.guardedRoot automaton state
      (fun term => decide (evaluateGuard operations solver guard (sourceTerm term) = .yes)))
    (FullGuardPrune.candidates operations solver automaton guard state)
  apply Iff.trans (exact ?_ ?_ ?_ result success term)
  · simpa using ObservationGraph.guardedRoot_accepts_iff automaton state
      (fun term => decide (evaluateGuard operations solver guard (sourceTerm term) = .yes)) term
  · intro term
    rw [ObservationGraph.guardedRoot_accepts_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨candidate, member, accepted, guardYes⟩
      obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
      exact ⟨(ObservationGraph.specialize_cover automaton _ _ state term).mp ⟨variant, present, accepted⟩, guardYes⟩
    · rintro ⟨accepted, guardYes⟩
      obtain ⟨variant, member, run⟩ := (ObservationGraph.specialize_cover automaton _ _ state term).mpr accepted
      exact ⟨_, List.mem_map.mpr ⟨variant, member, rfl⟩, run, guardYes⟩
  · intro candidate member proved term
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    constructor
    · intro accepted
      have view := (ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant present term accepted).2
      exact ⟨accepted, variant_decided model nullary laws sortDomain solver stable guard variant term view .yes (by decide) proved⟩
    · exact And.left
  · intro candidate member disproved term ⟨accepted, guardYes⟩
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    have view := (ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant present term accepted).2
    have no := variant_decided model nullary laws sortDomain solver stable guard variant term view .no (by decide) disproved
    have impossible := no.symm.trans guardYes
    cases impossible

end MicroCFTA.FullGuardPruneStable
