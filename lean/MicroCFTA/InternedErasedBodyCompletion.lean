import MicroCFTA.InternedErasedBodyResidual
import MicroCFTA.InternedNestedProvenance

/-!
# Enclosing binders complete after nested dependency erasure

The first depth execution supplies the actual complete nested records.
Later callbacks use the derived ordinary residual work while the outer
binder is pending. Changed discarded-edge keys retain their real effects.
-/
namespace MicroCFTA.InternedErasedBodyResidual
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedSpecialization InternedNestedCoverage InternedNestedFacts InternedNestedProvenance
open InternedProbeProvenance
open InternedErasedEdgeReplay (run_coherent)

/-- A binder with source-declared erased-dependent inner calls completes on its first execution. -/
theorem binder_completes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (admitted : Admitted expression) (captures : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (covered : Covered [] state) :
    ∃ value final, build (.binder smart expression) captures state = .done value final := by
  let callback := fun name current => (build expression (.reference name :: captures) current).bind
    fun value next => work (withoutSelfReference name value) next
  obtain ⟨initial, afterInitial, code, initialDone, initialCoherent, initialCovered, initialGrowth, safe, residual⟩ :=
    build_residual expression admitted (.reference .depth) captures state coherent covered
  let normalized := fun name => (code (.reference name)).bind (withoutSelfReference name)
  have normalizedSafe : ∀ name, Safe (normalized name) :=
    fun name => safe_bind _ _ (safe (.reference name)).1 (withoutSelfReference_safe name)
  have callbackWork : ∀ name after, Coherent after → Grows afterInitial after →
      callback name after = work (normalized name) after := by
    intro name after afterCoherent growth
    simp only [callback, residual (.reference name) after afterCoherent growth, normalized, work_bind]
  let depthResult := run (withoutSelfReference .depth initial) afterInitial
  have depthDone : callback .depth state = .done depthResult.1 depthResult.2 := by
    simp only [callback, initialDone, Outcome.bind, work, depthResult]
  have depthCoherent := run_coherent (withoutSelfReference .depth initial) afterInitial
    (withoutSelfReference_safe _ _) initialCoherent
  have depthCovered := run_covered (withoutSelfReference .depth initial) afterInitial initialCoherent.valid initialCovered
  have depthGrowth := (InternedConstructorTemplates.run_correct (withoutSelfReference .depth initial)
    afterInitial initialCoherent.valid).2
  let ordinaryResult := run (normalized (.uninterned depthResult.1.depth)) depthResult.2
  have ordinaryDone : callback (.uninterned depthResult.1.depth) depthResult.2 =
      .done ordinaryResult.1 ordinaryResult.2 := callbackWork _ _ depthCoherent depthGrowth
  have ordinaryCoherent := run_coherent (normalized (.uninterned depthResult.1.depth)) depthResult.2
    (normalizedSafe _) depthCoherent
  have ordinaryCovered := run_covered (normalized (.uninterned depthResult.1.depth)) depthResult.2 depthCoherent.valid depthCovered
  have ordinaryGrowth := (InternedConstructorTemplates.run_correct (normalized (.uninterned depthResult.1.depth))
    depthResult.2 depthCoherent.valid).2
  have expanded : build (.binder smart expression) captures state =
      (callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary := by rw [build]
  rw [expanded, depthDone]
  simp only [Outcome.bind]
  rw [ordinaryDone]
  cases present : ordinaryResult.2.nodes.table (muKey depthResult.1 ordinaryResult.1) with
  | some entry =>
      rcases ordinaryCovered.nodes _ entry present with impossible | ⟨record, stored⟩
      · cases impossible
      · change ordinaryResult.2.nodeRecords (muKey depthResult.1 ordinaryResult.1) = some record at stored
        simp only [request, present, stored]
        exact ⟨_, _, rfl⟩
  | none =>
      let key := muKey depthResult.1 ordinaryResult.1
      let entry := Cache.intern ordinaryResult.2.nodes key
      let allocated := {ordinaryResult.2 with nodes := entry.2}
      have allocatedCoherent := (reserve_correct key ordinaryResult.2 ordinaryCoherent ordinaryCovered).1
      have allocatedGrowth : Grows ordinaryResult.2 allocated :=
        ⟨Cache.extends_refl _, InternedBinderProtocol.intern_grows _ _, Cache.extends_refl _, Cache.extends_refl _⟩
      have actualDone := callbackWork (.interned entry.1.identity) allocated allocatedCoherent
        (grows_trans depthGrowth (grows_trans ordinaryGrowth allocatedGrowth))
      simp only [request, present]
      change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
      rw [actualDone]
      simp only [work, Outcome.bind]
      exact ⟨_, _, rfl⟩

/-- Closed source execution supplies the earlier nested requests itself before reserving the enclosing binder. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (admitted : Admitted expression) : ∃ value final, build (.binder smart expression) [] empty = .done value final :=
  binder_completes smart expression admitted [] empty empty_correct.1 empty_correct.2

/-- Erased-dependent first completion derives complete record provenance and exact whole-program replay. -/
theorem closed_complete_record [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (admitted : Admitted expression) :
    ∃ value final, build (.binder smart expression) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (.binder smart expression) [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes smart expression admitted
  have verified := closed_verified (.binder smart expression)
  refine ⟨value, final, completed, ?_, closed_covered _ value final completed,
    verified.result value final completed, fun after growth => empty_replay _ value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

end MicroCFTA.InternedErasedBodyResidual
