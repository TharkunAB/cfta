import MicroCFTA.SourceCurrentConjunctionRowsWarmEffects
import MicroCFTA.SourceCurrentConjunctionProjectionProbes

set_option autoImplicit false
open scoped Classical

/-! Probe and readiness preservation at actual conjunction endpoints. -/
namespace MicroCFTA.SourceCurrentConjunctionRowsProbes
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsWorker
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
variable {Symbol Formula A B : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Heap" => InternedFreshOrdinaryProbeHeap.Heap

private theorem map_state (actual : Outcome Symbol Formula A) (f : A → B) :
    (actual.bind fun value after => .done (f value) after).state = actual.state := by
  cases actual <;> rfl

private theorem bind_heap {actual : Outcome Symbol Formula A}
    {next : A → Physical → Outcome Symbol Formula B} (first : Heap actual.state.heap)
    (step : ∀ value after, actual = .done value after → Heap (next value after).state.heap) :
    Heap (actual.bind next).state.heap := by
  cases actual with
  | done value after => exact step value after rfl
  | failed fault after => exact first

/-- Every actual projection-list outcome retains clean Mu probes. -/
theorem projections_heap (p h : Nat) (jobs : List (Job Symbol Formula)) (before : Physical)
    (ready : Ready before) (probes : Heap before.heap)
    (available : ∀ job ∈ jobs, Values before.heap job.1) :
    Heap (projections p h jobs before).state.heap := by
  induction jobs generalizing before with
  | nil => exact probes
  | cons job jobs ih =>
    rcases job with ⟨forest, path⟩
    have own := available (forest, path) List.mem_cons_self
    have clean := SourceCurrentConjunctionProjectionProbes.forest_heap p h (path.map Int.ofNat) forest
      before.heap ready.semantic ready.costs probes own
    have first := SourceCurrentConjunctionProjectionWarmEffects.forest_effects p h (path.map Int.ofNat) forest before ready own
    cases read : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
    | done value heap =>
      rw [read] at clean first
      have kept : Effects before (⟨heap, before.equality⟩ : Physical) := first
      have now : Heap heap := clean
      have later := ih (⟨heap, before.equality⟩ : Physical) kept.ready now
        (fun job member child included => kept.keeps.available child (available job (List.mem_cons_of_mem _ member) child included))
      simpa only [projections, read, map_state] using later
    | pending key heap | unresolved key heap | exhausted key heap =>
      rw [read] at clean
      have now : Heap heap := clean
      simpa only [projections, read, Outcome.state] using now

/-- Every actual class-list outcome retains probes from its current forests. -/
theorem classes_heap (p h : Nat) (forests : List (List (Value Symbol Guard)))
    (constraints : EqualityNormalize.Constraints) (before : Physical) (ready : Ready before)
    (probes : Heap before.heap) (available : ∀ forest ∈ forests, Values before.heap forest) :
    Heap (classes p h forests constraints before).state.heap := by
  induction constraints generalizing before with
  | nil => exact probes
  | cons paths constraints ih =>
    have inputs : ∀ job ∈ SourceCurrentConjunctionCompletionReads.jobs forests paths, Values before.heap job.1 := by
      intro job member
      obtain ⟨children, present, selected⟩ := List.mem_flatMap.mp member
      obtain ⟨path, _, rfl⟩ := List.mem_map.mp selected
      exact available children present
    have clean := projections_heap p h (SourceCurrentConjunctionCompletionReads.jobs forests paths) before ready probes inputs
    have first := SourceCurrentConjunctionRowsWarmEffects.projections_effects p h
      (SourceCurrentConjunctionCompletionReads.jobs forests paths) before ready inputs
    rw [classes]
    apply bind_heap clean
    intro projected middle completed
    have kept : Effects before middle := by simpa only [completed, Outcome.state] using first
    have later := ih middle kept.ready
      (by simpa only [completed, Outcome.state] using clean)
      (fun forest member child included => kept.keeps.available child (available forest member child included))
    simpa only [map_state] using later

/-- Every actual requirement outcome retains probes from resident tuple rows. -/
theorem requirements_heap (p h : Nat) (edges : List (EdgeValue Symbol Guard))
    (constraints : EqualityNormalize.Constraints) (before : Physical) (ready : Ready before)
    (probes : Heap before.heap) (resident : Edges before.heap edges) :
    Heap (requirements p h edges constraints before).state.heap := by
  have available : ∀ forest ∈ edges.map EdgeValue.children, Values before.heap forest := by
    intro forest member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
    intro child included
    exact ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge present) child included
  simpa only [requirements, map_state] using
    classes_heap p h (edges.map EdgeValue.children) constraints before ready probes available

/-- Cache folding keeps the initial heap before actual requirement allocation. -/
theorem tuple_heap (p h : Nat) (edges : List (EdgeValue Symbol Guard)) (before : Physical)
    (ready : Ready before) (probes : Heap before.heap) (resident : Edges before.heap edges) :
    Heap (tuple p h edges before).state.heap := by
  obtain ⟨result, folded, valid, _, _, _, growth⟩ := SourceCurrentConjunctionEquality.fold_correct edges before.equality ready.valid
    (fun edge member => ready.fields edge.entry.key edge (resident edge member))
  let current : Physical := ⟨before.heap, (SourceCurrentConjunctionEquality.fold edges before.equality).2⟩
  have now : Ready current := ⟨ready.semantic, ready.costs, valid, ready.fields.grows growth⟩
  cases selected : SourceEqualityInheritedPayload.classes result.payload with
  | none => simpa only [tuple, folded, selected, Outcome.state] using probes
  | some constraints =>
    simpa only [tuple, folded, selected, map_state] using
      requirements_heap p h edges constraints current now probes resident

/-- Every actual tuple-list outcome retains clean Mu probes at its reached heap. -/
theorem tuples_heap (p h : Nat) (tuples : List (List (EdgeValue Symbol Guard))) (before : Physical)
    (ready : Ready before) (probes : Heap before.heap) (resident : ∀ edges ∈ tuples, Edges before.heap edges) :
    Heap (SourceCurrentConjunctionRowsWorker.tuples p h tuples before).state.heap := by
  induction tuples generalizing before with
  | nil => exact probes
  | cons edges remaining ih =>
    have clean := tuple_heap p h edges before ready probes (resident edges List.mem_cons_self)
    have first := SourceCurrentConjunctionRowsWarmEffects.tuple_effects p h edges before ready (resident edges List.mem_cons_self)
    rw [SourceCurrentConjunctionRowsWorker.tuples]
    apply bind_heap clean
    intro row middle completed
    have kept : Effects before middle := by simpa only [completed, Outcome.state] using first
    have later := ih middle kept.ready (by simpa only [completed, Outcome.state] using clean)
      (fun edges member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap kept.keeps.growth edge
        (resident edges (List.mem_cons_of_mem _ member) edge included))
    simpa only [map_state] using later

/-- Literal exposure, matching tuples, and allocated rows retain clean Mu probes. -/
theorem rows_heap (p h : Nat) (nodes : List (Value Symbol Guard)) (before : Physical)
    (ready : Ready before) (probes : Heap before.heap) (available : Values before.heap nodes) :
    Heap (SourceCurrentConjunctionRowsWorker.rows p h nodes before).state.heap := by
  have clean := SourceCurrentConjunctionExposureProbes.exposures_heap h nodes before ready.semantic ready.costs probes available
  have first := SourceCurrentConjunctionRowsExposureFields.exposures_effects h nodes before ready available
  unfold SourceCurrentConjunctionRowsWorker.rows
  apply bind_heap clean
  intro rows middle completed
  have kept : Effects before middle := by simpa only [completed, Outcome.state] using first.1
  have exposed := first.2
  rw [completed] at exposed
  have resident : ∀ edges ∈ SourceCurrentConjunctionTuples.tuples rows, Edges middle.heap edges := by
    intro edges member edge included
    obtain ⟨row, present, own⟩ := List.mem_flatten.mp
      (SourceCurrentConjunctionTuples.tuples_members rows edges member edge included)
    exact (exposed row present).1 edge own
  exact tuples_heap p h (SourceCurrentConjunctionTuples.tuples rows) middle kept.ready
    (by simpa only [completed, Outcome.state] using clean) resident

end MicroCFTA.SourceCurrentConjunctionRowsProbes
