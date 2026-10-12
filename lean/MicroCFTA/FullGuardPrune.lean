import MicroCFTA.NoConflictKnown
import MicroCFTA.PruneCandidates

/-!
# Graph pruning with the complete current guard evaluator

This bridge uses the proved finite-plan graph specialization and the source
candidate loop. It covers every Guard constructor. The preservation theorem
requires conflict-free actual names in the generated cells. That check is
concrete; no whole-guard correctness premise is assumed.
-/
namespace MicroCFTA.FullGuardPrune
open SourceGuards SourceObservations

/-- Change only the label representation from graph fields to evaluator pairs. -/
def sourceTerm : Language.Term (Observation.Label Name Formula) → Language.Term (Label Formula)
  | .node label children => .node (label.symbol, label.refinement) (children.map sourceTerm)

/-- Label conversion commutes with complete position lookup. -/
theorem sourceTerm_path (term : Language.Term (Observation.Label Name Formula)) (path : Path) :
    Language.Term.atPath (sourceTerm term) path = (Language.Term.atPath term path).map sourceTerm := by
  induction path generalizing term with
  | nil => rfl
  | cons index rest ih =>
      cases term with
      | node label children =>
          simp only [sourceTerm, Language.Term.atPath, List.getElem?_map]
          cases found : children[index]? <;> simp [ih]

/-- A stored complete graph observation has the same source symbol and shape. -/
def sourceObserved (observed : Observation.Observed Name Formula) : Observed Formula :=
  ⟨observed.label.symbol, observed.label.refinement, if observed.leaf then .leaf else .inner⟩

theorem sourceTerm_root (term : Language.Term (Observation.Label Name Formula)) :
    rootObservation (sourceTerm term) = sourceObserved (Observation.rootObservation term) := by
  cases term with
  | node label children => simp [sourceTerm, rootObservation, sourceObserved, Observation.rootObservation]

/-- Refinement-only signature entries can use any constructor and shape outside structural reads. -/
def decodeEntry : Observation.Entry Name Formula → Observed Formula
  | .refinement formula => ⟨"", formula, .mixed⟩
  | .symbol observed => sourceObserved observed

/-- Reconstruct exactly the information the current guard requires from a variant signature. -/
def queryObservations (view : Path → Option (Observation.Entry Name Formula)) : Observations Formula :=
  fun path => (view path).map decodeEntry

/-- Exact graph signatures provide every required refinement and complete symbol read. -/
theorem signature_reads (guard : Guard Formula) (term : Language.Term (Observation.Label Name Formula)) :
    SourceReadAgreement.Reads guard
      (queryObservations (Observation.signature (SourceGuardPlan.plan guard) term)) (observe (sourceTerm term)) := by
  constructor
  · intro path requested
    simp only [queryObservations, Observation.signature, Observation.readWith_correct,
      SourceGuardPlan.lookup_plan, requested, ↓reduceIte, Option.bind_some,
      observe, sourceTerm_path, Option.map_map]
    cases needed : SourceGuardPlan.need guard path <;> cases found : term.atPath path <;>
      simp [Observation.signatureEntry, decodeEntry, sourceTerm_root, sourceObserved]
  · intro path sensitive
    have requested := SourceReadAgreement.sensitive_requested guard path sensitive
    simp only [queryObservations, Observation.signature, Observation.readWith_correct,
      SourceGuardPlan.lookup_plan, requested, ↓reduceIte, Option.bind_some,
      observe, sourceTerm_path, Option.map_map]
    have needed : SourceGuardPlan.need guard path = .symbol := by simp [SourceGuardPlan.need, sensitive]
    rw [needed]
    cases found : term.atPath path <;>
      simp [Observation.signatureEntry, decodeEntry, sourceTerm_root]

/-- A conflict-free stored variant view has the same sparse guard result as every represented term. -/
theorem view_evaluator_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (view : Path → Option (Observation.Entry Name Formula))
    (term : Language.Term (Observation.Label Name Formula))
    (exactView : view = Observation.signature (SourceGuardPlan.plan guard) term)
    (noConflict : conflicts (queryObservations view) (sameShape formulas (queryObservations view) []) guard = []) :
    evaluateGuardWithShape formulas solver (queryObservations view) guard =
      evaluateGuardWithShape formulas solver (observe (sourceTerm term)) guard := by
  have reads : SourceReadAgreement.Reads guard (queryObservations view) (observe (sourceTerm term)) :=
    exactView ▸ signature_reads guard term
  unfold evaluateGuardWithShape evaluateGuardWithSame
  rw [SourceIdentityReads.no_conflict_tables_reads formulas guard _ _ reads noConflict]
  exact SourceReadAgreement.evaluate_reads formulas solver _ _ _ _ [] true guard reads

/-- A decided conflict-free variant query equals complete public guard evaluation for its represented term. -/
theorem view_decided_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (view : Path → Option (Observation.Entry Name Formula))
    (term : Language.Term (Observation.Label Name Formula))
    (exactView : view = Observation.signature (SourceGuardPlan.plan guard) term)
    (noConflict : conflicts (queryObservations view) (sameShape formulas (queryObservations view) []) guard = [])
    (decided : evaluateGuardWithShape formulas solver (queryObservations view) guard ≠ .unknown) :
    evaluateGuardWithShape formulas solver (queryObservations view) guard =
      evaluateGuard formulas solver guard (sourceTerm term) := by
  have reads : SourceReadAgreement.Reads guard (queryObservations view) (observe (sourceTerm term)) :=
    exactView ▸ signature_reads guard term
  have termConflict : conflicts (observe (sourceTerm term)) (sameShape formulas (observe (sourceTerm term)) []) guard = [] :=
    (SourceIdentityReads.conflicts_reads formulas guard _ _ reads).symm.trans noConflict
  rw [view_evaluator_exact formulas solver guard view term exactView noConflict] at decided ⊢
  exact SourceGuardRefinement.unambiguous_decided_exact formulas solver (sourceTerm term) guard
    (NoConflictKnown.no_conflicts_known formulas _ guard termConflict) decided

/-- Run the actual source sparse guard on a finite graph variant. -/
def variantVerdict [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (variant : ObservationGraph.Variant State Name Formula) : Guards.Verdict :=
  PruneSchedule.safeVerdict
    (!(ambiguous (queryObservations variant.view) (fun _ _ => none) guard).isEmpty)
    (evaluateGuardWithShape formulas solver (queryObservations variant.view) guard)

/-- Build source candidates from the exact finite-plan graph specialization. -/
def candidates [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (automaton : Language.Automaton State (Observation.Label Name Formula)) (guard : Guard Formula) (state : State) :
    List (PruneSchedule.Candidate (ObservationGraph.Node State (Observation.Label Name Formula))) :=
  (ObservationGraph.specialize automaton (ObservationGraph.planBudget (SourceGuardPlan.plan guard))
    (SourceGuardPlan.plan guard) state).map (fun variant =>
      ⟨variant.node, variantVerdict formulas solver guard variant,
       !(ambiguous (queryObservations variant.view) (fun _ _ => none) guard).isEmpty⟩)

/-- Execute the complete source candidate loop and preserve the original full guard on fallback. -/
def prune [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (automaton : Language.Automaton State (Observation.Label Name Formula)) (guard : Guard Formula) (state : State) :
    Except PruneSchedule.Error (List (ObservationGraph.Node State (Observation.Label Name Formula))) :=
  PruneSchedule.check
    (ObservationGraph.guardedRoot automaton state
      (fun term => decide (evaluateGuard formulas solver guard (sourceTerm term) = .yes))) []
    (candidates formulas solver automaton guard state)

/-- Successful source candidate pruning preserves every confirmed term for full conflict-free guards. -/
theorem prune_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (automaton : Language.Automaton State (Observation.Label Name Formula)) (guard : Guard Formula) (state : State)
    (noConflict : ∀ variant ∈ ObservationGraph.specialize automaton
        (ObservationGraph.planBudget (SourceGuardPlan.plan guard)) (SourceGuardPlan.plan guard) state,
      conflicts (queryObservations variant.view) (sameShape formulas (queryObservations variant.view) []) guard = [])
    (result : List (ObservationGraph.Node State (Observation.Label Name Formula)))
    (success : prune formulas solver automaton guard state = .ok result)
    (term : Language.Term (Observation.Label Name Formula)) :
    PruneCandidates.Denotes (ObservationGraph.AcceptsNode automaton) result term ↔
      Language.Accepts automaton state term ∧ evaluateGuard formulas solver guard (sourceTerm term) = .yes := by
  have exact := PruneCandidates.check_exact (ObservationGraph.AcceptsNode automaton)
    (fun candidate term => ObservationGraph.AcceptsNode automaton candidate.edge term ∧
      evaluateGuard formulas solver guard (sourceTerm term) = .yes)
    (ObservationGraph.guardedRoot automaton state
      (fun term => decide (evaluateGuard formulas solver guard (sourceTerm term) = .yes)))
    (candidates formulas solver automaton guard state)
  apply Iff.trans (exact ?_ ?_ ?_ result success term)
  · simpa using ObservationGraph.guardedRoot_accepts_iff automaton state
      (fun term => decide (evaluateGuard formulas solver guard (sourceTerm term) = .yes)) term
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
    change variantVerdict formulas solver guard variant = .yes at proved
    have proved := (PruneSchedule.safeVerdict_yes _ _).mp proved |>.2
    constructor
    · intro accepted
      have view := (ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant present term accepted).2
      have decision := view_decided_exact formulas solver guard variant.view term view (noConflict variant present)
        (by rw [proved]; decide)
      exact ⟨accepted, decision.symm.trans proved⟩
    · exact And.left
  · intro candidate member disproved term ⟨accepted, guardYes⟩
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    change variantVerdict formulas solver guard variant = .no at disproved
    have disproved := (PruneSchedule.safeVerdict_no _ _).mp disproved |>.2
    have view := (ObservationGraph.specialize_exact automaton (SourceGuardPlan.plan guard) state variant present term accepted).2
    have decision := view_decided_exact formulas solver guard variant.view term view (noConflict variant present)
      (by rw [disproved]; decide)
    have impossible := disproved.symm.trans (decision.trans guardYes)
    cases impossible

end MicroCFTA.FullGuardPrune
