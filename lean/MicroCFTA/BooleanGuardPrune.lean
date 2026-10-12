import MicroCFTA.FullGuardPruneStable
import MicroCFTA.SourceBooleanBridge

/-!
# Historical blanket ambiguity gate in candidate pruning

This model retains the earlier unconditional ambiguity gate. The current
source evaluates first and uses ambiguity only after Unknown.
`CurrentGuardPrune` models that policy and states its remaining proof scope.
Exact preservation also needs the stated backend name-transport contract.
-/
namespace MicroCFTA.BooleanGuardPrune
open FullSyntax SourceFormula SourceGuards SourceObservations FullGuardPrune

/-- Run the actual source sparse guard on a finite graph variant. -/
def variantVerdict [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (variant : ObservationGraph.Variant State String Formula) : Guards.Verdict :=
  PruneSchedule.safeVerdict
    (!(ambiguous (queryObservations variant.view) (fun _ _ => none) guard).isEmpty)
    (SourceBooleanEntry.evaluateGuardWithShape formulas solver (queryObservations variant.view) guard)

/-- Build source candidates from the exact finite-plan graph specialization. -/
def candidates [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State) :
    List (PruneSchedule.Candidate (ObservationGraph.Node State (Observation.Label String Formula))) :=
  (ObservationGraph.specialize automaton (ObservationGraph.planBudget (SourceGuardPlan.plan guard))
    (SourceGuardPlan.plan guard) state).map (fun variant =>
      ⟨variant.node, variantVerdict formulas solver guard variant,
       !(ambiguous (queryObservations variant.view) (fun _ _ => none) guard).isEmpty⟩)

/-- Execute the complete source candidate loop and preserve the original full guard on fallback. -/
def prune [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State) :
    Except PruneSchedule.Error (List (ObservationGraph.Node State (Observation.Label String Formula))) :=
  PruneSchedule.check
    (ObservationGraph.guardedRoot automaton state
      (fun term => decide (SourceBooleanEntry.evaluateGuard formulas solver guard (sourceTerm term) = .yes))) []
    (candidates formulas solver automaton guard state)

/-- Every decided safe variant agrees with complete evaluation of its represented terms. -/
theorem variant_decided (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (variant : ObservationGraph.Variant State String Formula)
    (term : Language.Term (Observation.Label String Formula))
    (view : variant.view = Observation.signature (SourceGuardPlan.plan guard) term)
    (answer : Guards.Verdict) (decided : answer ≠ .unknown)
    (found : variantVerdict operations solver guard variant = answer) :
    SourceBooleanEntry.evaluateGuard operations solver guard (sourceTerm term) = answer := by
  have gateClear : ambiguous (queryObservations variant.view) (fun _ _ => none) guard = [] := by
    unfold variantVerdict PruneSchedule.safeVerdict at found
    split at found
    · exact False.elim (decided found.symm)
    · rename_i empty
      simpa using empty
  have clear := FullGuardPruneStable.gate_unambiguous operations (queryObservations variant.view) guard gateClear
  have raw : SourceBooleanEntry.evaluateGuardWithShape operations solver (queryObservations variant.view) guard = answer := by
    simpa [variantVerdict, gateClear, PruneSchedule.safeVerdict] using found
  have reads : SourceReadAgreement.Reads guard (queryObservations variant.view) (observe (sourceTerm term)) :=
    view ▸ signature_reads guard term
  exact (SourceBooleanBridge.complete_decision model nullary laws sortDomain solver stable guard _ (sourceTerm term) reads clear
    (fun unknown => decided (raw.symm.trans unknown))).symm.trans raw

/-- Every successful full-guard candidate pass preserves all confirmed terms, including fresh-name conflicts and ambiguity fallback. -/
theorem prune_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term ↔
      Language.Accepts automaton state term ∧ SourceBooleanEntry.evaluateGuard operations solver guard (sourceTerm term) = .yes := by
  have exact := PruneCandidates.check_exact (ObservationGraph.AcceptsNode automaton)
    (fun candidate term => ObservationGraph.AcceptsNode automaton candidate.edge term ∧
      SourceBooleanEntry.evaluateGuard operations solver guard (sourceTerm term) = .yes)
    (ObservationGraph.guardedRoot automaton state
      (fun term => decide (SourceBooleanEntry.evaluateGuard operations solver guard (sourceTerm term) = .yes)))
    (candidates operations solver automaton guard state)
  apply Iff.trans (exact ?_ ?_ ?_ result success term)
  · simpa using ObservationGraph.guardedRoot_accepts_iff automaton state
      (fun term => decide (SourceBooleanEntry.evaluateGuard operations solver guard (sourceTerm term) = .yes)) term
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

end MicroCFTA.BooleanGuardPrune
