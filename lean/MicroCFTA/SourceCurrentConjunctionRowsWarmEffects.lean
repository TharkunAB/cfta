import MicroCFTA.SourceCurrentConjunctionProjectionWarmEffects
import MicroCFTA.SourceCurrentConjunctionRowsExposureFields

set_option autoImplicit false
open scoped Classical

/-! Full readiness at every actual rows outcome. -/
namespace MicroCFTA.SourceCurrentConjunctionRowsWarmEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsWorker
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
variable {Symbol Formula A B : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula

private theorem map_state (actual : Outcome Symbol Formula A) (f : A → B) :
    (actual.bind fun value after => .done (f value) after).state = actual.state := by
  cases actual <;> rfl

private theorem bind_effects {before : Physical} {actual : Outcome Symbol Formula A}
    {next : A → Physical → Outcome Symbol Formula B} (first : Effects before actual.state)
    (step : ∀ value after, actual = .done value after → Effects after (next value after).state) :
    Effects before (actual.bind next).state := by
  cases actual with
  | done value after => exact first.trans (step value after rfl)
  | failed fault after => exact first

private theorem projections_core (p h : Nat) (jobs : List (Job Symbol Formula)) (before : Physical)
    (ready : Ready before) (available : ∀ job ∈ jobs, Values before.heap job.1) :
    let actual := projections p h jobs before
    Effects before actual.state ∧
      ∀ values after, actual = .done values after → Values after.heap values := by
  induction jobs generalizing before with
  | nil =>
    refine ⟨Effects.refl before ready, ?_⟩
    intro values after completed
    cases completed
    intro value member
    cases member
  | cons job jobs ih =>
    rcases job with ⟨forest, path⟩
    have own := available (forest, path) List.mem_cons_self
    have first := SourceCurrentConjunctionProjectionWarmEffects.forest_effects p h (path.map Int.ofNat) forest before ready own
    cases read : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
    | done value heap =>
      have kept : Effects before (⟨heap, before.equality⟩ : Physical) := by
        rw [read] at first
        exact first
      have graph := SourceEqualityProjectionWorkerSound.forest_graph p h (path.map Int.ofNat) forest before.heap value heap read
      have present := (SourceEqualityProjectionCosts.forest_effects graph ready.semantic ready.costs own).2.2.2
      have later := ih (⟨heap, before.equality⟩ : Physical) kept.ready
        (fun job member child included => kept.keeps.available child (available job (List.mem_cons_of_mem _ member) child included))
      cases suffix : projections p h jobs (⟨heap, before.equality⟩ : Physical) with
      | done values after =>
        have tail : Effects (⟨heap, before.equality⟩ : Physical) after := by simpa only [suffix, Outcome.state] using later.1
        simp only [projections, read, suffix, Outcome.bind, Outcome.state]
        refine ⟨kept.trans tail, ?_⟩
        intro output final completed
        cases completed
        intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact tail.keeps.available _ present
        · exact later.2 values after suffix child member
      | failed fault after =>
        have tail : Effects (⟨heap, before.equality⟩ : Physical) after := by simpa only [suffix, Outcome.state] using later.1
        simp only [projections, read, suffix, Outcome.bind, Outcome.state]
        exact ⟨kept.trans tail, by intro values final completed; cases completed⟩
    | pending key heap | unresolved key heap | exhausted key heap =>
      have kept : Effects before (⟨heap, before.equality⟩ : Physical) := by
        rw [read] at first
        exact first
      simp only [projections, read, Outcome.state]
      exact ⟨kept, by intro values after completed; cases completed⟩

/-- Actual job-list projection retains the full reached physical invariant. -/
theorem projections_effects (p h : Nat) (jobs : List (Job Symbol Formula)) (before : Physical)
    (ready : Ready before) (available : ∀ job ∈ jobs, Values before.heap job.1) :
    Effects before (projections p h jobs before).state :=
  (projections_core p h jobs before ready available).1

/-- Actual completed projections produce available values in their reached heap. -/
theorem projections_available (p h : Nat) (jobs : List (Job Symbol Formula)) (before : Physical)
    (ready : Ready before) (available : ∀ job ∈ jobs, Values before.heap job.1) :
    let actual := projections p h jobs before
    match actual with | .done values after => Values after.heap values | .failed _ _ => True := by
  have checked := projections_core p h jobs before ready available
  cases actual : projections p h jobs before with
  | done values after => exact checked.2 values after actual
  | failed fault after => trivial

/-- Class projection derives every job admission from its current operand forests. -/
theorem classes_effects (p h : Nat) (forests : List (List (Value Symbol Guard)))
    (constraints : EqualityNormalize.Constraints) (before : Physical) (ready : Ready before)
    (available : ∀ forest ∈ forests, Values before.heap forest) :
    Effects before (classes p h forests constraints before).state := by
  induction constraints generalizing before with
  | nil => exact Effects.refl before ready
  | cons paths constraints ih =>
    have inputs : ∀ job ∈ SourceCurrentConjunctionCompletionReads.jobs forests paths, Values before.heap job.1 := by
      intro job member
      obtain ⟨children, present, selected⟩ := List.mem_flatMap.mp member
      obtain ⟨path, _, rfl⟩ := List.mem_map.mp selected
      exact available children present
    have first := projections_effects p h (SourceCurrentConjunctionCompletionReads.jobs forests paths) before ready inputs
    rw [classes]
    apply bind_effects first
    intro projected middle completed
    have kept : Effects before middle := by simpa only [completed, Outcome.state] using first
    have later := ih middle kept.ready
      (fun forest member child included => kept.keeps.available child (available forest member child included))
    simpa only [map_state] using later

/-- Resident tuple rows derive current inputs for every live requirement projection. -/
theorem requirements_effects (p h : Nat) (edges : List (EdgeValue Symbol Guard))
    (constraints : EqualityNormalize.Constraints) (before : Physical) (ready : Ready before)
    (resident : Edges before.heap edges) :
    Effects before (requirements p h edges constraints before).state := by
  have available : ∀ forest ∈ edges.map EdgeValue.children, Values before.heap forest := by
    intro forest member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
    intro child included
    exact ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge present) child included
  simpa only [requirements, map_state] using
    classes_effects p h (edges.map EdgeValue.children) constraints before ready available

/-- Actual fold state supplies current readiness before any requirement allocation. -/
theorem tuple_effects (p h : Nat) (edges : List (EdgeValue Symbol Guard)) (before : Physical)
    (ready : Ready before) (resident : Edges before.heap edges) :
    Effects before (tuple p h edges before).state := by
  obtain ⟨result, folded, valid, _, _, _, growth⟩ := SourceCurrentConjunctionEquality.fold_correct edges before.equality ready.valid
    (fun edge member => ready.fields edge.entry.key edge (resident edge member))
  let current : Physical := ⟨before.heap, (SourceCurrentConjunctionEquality.fold edges before.equality).2⟩
  have now : Ready current := ⟨ready.semantic, ready.costs, valid, ready.fields.grows growth⟩
  have first : Effects before current := ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready, now, growth⟩
  cases selected : SourceEqualityInheritedPayload.classes result.payload with
  | none => simpa only [tuple, folded, selected, Outcome.state] using first
  | some constraints =>
    simpa only [tuple, folded, selected, map_state] using
      first.trans (requirements_effects p h edges constraints current now resident)

/-- Every tuple-list outcome retains full readiness at its actual returned state. -/
theorem tuples_effects (p h : Nat) (tuples : List (List (EdgeValue Symbol Guard))) (before : Physical)
    (ready : Ready before) (resident : ∀ edges ∈ tuples, Edges before.heap edges) :
    Effects before (SourceCurrentConjunctionRowsWorker.tuples p h tuples before).state := by
  induction tuples generalizing before with
  | nil => exact Effects.refl before ready
  | cons edges remaining ih =>
    have first := tuple_effects p h edges before ready (resident edges List.mem_cons_self)
    rw [SourceCurrentConjunctionRowsWorker.tuples]
    apply bind_effects first
    intro row middle completed
    have kept : Effects before middle := by simpa only [completed, Outcome.state] using first
    have later := ih middle kept.ready (fun edges member edge included =>
      InternedEdgeResidency.edge_grows before.heap middle.heap kept.keeps.growth edge
        (resident edges (List.mem_cons_of_mem _ member) edge included))
    simpa only [map_state] using later

/-- Literal exposure, matching tuples, and allocated rows retain full reached readiness. -/
theorem rows_effects (p h : Nat) (nodes : List (Value Symbol Guard)) (before : Physical)
    (ready : Ready before) (available : Values before.heap nodes) :
    Effects before (SourceCurrentConjunctionRowsWorker.rows p h nodes before).state := by
  have first := SourceCurrentConjunctionRowsExposureFields.exposures_effects h nodes before ready available
  unfold SourceCurrentConjunctionRowsWorker.rows
  apply bind_effects first.1
  intro rows middle completed
  have kept : Effects before middle := by simpa only [completed, Outcome.state] using first.1
  have exposed := first.2
  rw [completed] at exposed
  have resident : ∀ edges ∈ SourceCurrentConjunctionTuples.tuples rows, Edges middle.heap edges := by
    intro edges member edge included
    obtain ⟨row, present, own⟩ := List.mem_flatten.mp
      (SourceCurrentConjunctionTuples.tuples_members rows edges member edge included)
    exact (exposed row present).1 edge own
  exact tuples_effects p h (SourceCurrentConjunctionTuples.tuples rows) middle kept.ready resident

end MicroCFTA.SourceCurrentConjunctionRowsWarmEffects
