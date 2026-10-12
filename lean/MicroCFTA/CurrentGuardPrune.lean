import MicroCFTA.FullGuardPruneStable
import MicroCFTA.SourceSubstitutionPrecedence

/-!
# Current candidate pruning after the substitution safeguards

The source evaluates the sparse guard first. Ambiguity affects only an
Unknown result. Exactness below covers specialization cells whose actual
table is unambiguous. General accepted ambiguous cells require the missing
one-way query transport; there is no source precheck for that premise.
-/
namespace MicroCFTA.CurrentGuardPrune
open FullSyntax SourceFormula SourceGuards SourceObservations FullGuardPrune

/-- Run the actual source sparse guard on a finite graph variant. -/
def variantVerdict [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (variant : ObservationGraph.Variant State String Formula) : Guards.Verdict :=
  SourceSubstitutionPrecedence.evaluateGuardWithShape formulas solver (queryObservations variant.view) guard

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
      (fun term => decide (SourceSubstitutionPrecedence.evaluateGuard formulas solver guard (sourceTerm term) = .yes))) []
    (candidates formulas solver automaton guard state)

/-- Every decided safe variant agrees with complete evaluation of its represented terms. -/
theorem variant_decided (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (variant : ObservationGraph.Variant State String Formula)
    (term : Language.Term (Observation.Label String Formula))
    (view : variant.view = Observation.signature (SourceGuardPlan.plan guard) term)
    (unambiguous : ambiguous (queryObservations variant.view)
      (sameShape operations (queryObservations variant.view) []) guard = [])
    (answer : Guards.Verdict) (decided : answer ≠ .unknown)
    (found : variantVerdict operations solver guard variant = answer) :
    SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = answer := by
  have current := SourceSubstitutionPrecedence.public_known operations solver (queryObservations variant.view)
    (sameShape operations (queryObservations variant.view)) true guard unambiguous
  change SourceSubstitutionPrecedence.evaluateGuardWithShape operations solver (queryObservations variant.view) guard =
    SourceBooleanEntry.evaluateGuardWithShape operations solver (queryObservations variant.view) guard at current
  have raw : SourceBooleanEntry.evaluateGuardWithShape operations solver (queryObservations variant.view) guard = answer :=
    current.symm.trans found
  have reads : SourceReadAgreement.Reads guard (queryObservations variant.view) (observe (sourceTerm term)) :=
    view ▸ signature_reads guard term
  rw [SourceSubstitutionPrecedence.complete_unchanged]
  exact (SourceBooleanBridge.complete_decision model nullary laws sortDomain solver stable guard _ (sourceTerm term) reads
    unambiguous (fun unknown => decided (raw.symm.trans unknown))).symm.trans raw

/-- Successful pruning preserves all confirmed terms on unambiguous specialization cells. -/
theorem prune_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (automaton : Language.Automaton State (Observation.Label String Formula)) (guard : Guard Formula) (state : State)
    (unambiguous : ∀ variant ∈ ObservationGraph.specialize automaton
      (ObservationGraph.planBudget (SourceGuardPlan.plan guard)) (SourceGuardPlan.plan guard) state,
      ambiguous (queryObservations variant.view)
        (sameShape operations (queryObservations variant.view) []) guard = [])
    (result : List (ObservationGraph.Node State (Observation.Label String Formula)))
    (success : prune operations solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label String Formula)) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term ↔
      Language.Accepts automaton state term ∧ SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes := by
  have exact := PruneCandidates.check_exact (ObservationGraph.AcceptsNode automaton)
    (fun candidate term => ObservationGraph.AcceptsNode automaton candidate.edge term ∧
      SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes)
    (ObservationGraph.guardedRoot automaton state
      (fun term => decide (SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes)))
    (candidates operations solver automaton guard state)
  apply Iff.trans (exact ?_ ?_ ?_ result success term)
  · simpa using ObservationGraph.guardedRoot_accepts_iff automaton state
      (fun term => decide (SourceSubstitutionPrecedence.evaluateGuard operations solver guard (sourceTerm term) = .yes)) term
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
      exact ⟨accepted, variant_decided model nullary laws sortDomain solver stable guard variant term view (unambiguous variant present) .yes (by decide) proved⟩
    · exact And.left
  · intro candidate member disproved term ⟨accepted, guardYes⟩
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    have view := (ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant present term accepted).2
    have no := variant_decided model nullary laws sortDomain solver stable guard variant term view (unambiguous variant present) .no (by decide) disproved
    have impossible := no.symm.trans guardYes
    cases impossible

/-- The same-scope witness also triggers the source's conservative fallback flag. -/
theorem same_scope_ambiguous :
    (!(ambiguous (observe NestedScopeCapture.term) (fun _ _ => none) SameScopeIdentityCapture.guard).isEmpty) = true := by
  have table := congrArg Prod.snd SameScopeIdentityCapture.tables.1
  change ambiguous (observe NestedScopeCapture.term)
    (sameShape operations (observe NestedScopeCapture.term) []) SameScopeIdentityCapture.guard = [[0], [1]] at table
  cases found : ambiguous (observe NestedScopeCapture.term) (fun _ _ => none) SameScopeIdentityCapture.guard with
  | nil =>
      have impossible := FullGuardPruneStable.gate_unambiguous operations (observe NestedScopeCapture.term)
        SameScopeIdentityCapture.guard found
      rw [table] at impossible
      cases impossible
  | cons first rest => rfl

/-- The repaired sparse witness restores the original edge, including any prior retained candidates. -/
theorem same_scope_restores (original edge : Edge) (prior suffix : List (PruneSchedule.Candidate Edge))
    (complete : ∀ candidate ∈ prior, candidate.verdict ≠ .unknown) (retained : List Edge) :
    PruneSchedule.check original retained (prior ++
      ⟨edge, SourceSubstitutionPrecedence.evaluateGuardWithShape operations NestedScopeCapture.solver
        (observe NestedScopeCapture.term) SameScopeIdentityCapture.guard,
       !(ambiguous (observe NestedScopeCapture.term) (fun _ _ => none) SameScopeIdentityCapture.guard).isEmpty⟩ :: suffix) =
      .ok [original] := by
  rw [SourceSubstitutionPrecedence.same_scope_unknown, same_scope_ambiguous]
  exact PruneSchedule.ambiguous_restores original prior suffix complete edge retained

end MicroCFTA.CurrentGuardPrune
