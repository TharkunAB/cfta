import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual

namespace MicroCFTA.CurrentConjunctionRowsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker
open SourceCurrentConjunctionRowsWorkerCompletion
open SourceCurrentConjunctionRowsWorkerStability (rows_done_unique)
open SourceCurrentConjunctionRowsWorkerActual (rows_graph rows_finite rows_verified)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A contradictory tuple performs no projection even with zero read and projection bounds. -/
theorem contradiction_skips_projection_at_zero
    {edges : List (EdgeValue Symbol Guard)} {before : Physical Symbol Formula}
    {result : SourceEqualityConstraintAllocation.Value}
    (folded : (SourceCurrentConjunctionEquality.fold edges before.equality).1 = .ok (some result))
    (empty : SourceEqualityInheritedPayload.classes result.payload = none) :
    tuple 0 0 edges before = .done none ⟨before.heap, (SourceCurrentConjunctionEquality.fold edges before.equality).2⟩ ∧
      StableRun (fun p h => tuple p h edges before) none
        ⟨before.heap, (SourceCurrentConjunctionEquality.fold edges before.equality).2⟩ := by
  exact ⟨by simp only [tuple, folded, empty], tuple_complete (.contradiction folded empty)⟩

/-- The standalone requirements worker adds no check that is absent from the source. -/
theorem unequal_arity_requires_explicit_graph_scope
    (edges : List (EdgeValue Symbol Guard)) (before : Physical Symbol Formula)
    (unequal : ¬ SourceCurrentConjunctionRequirements.SameArity edges) :
    requirements 0 0 edges [] before = .done
      ((SourceCurrentConjunctionRequirements.columns edges).map SourceCurrentConjunctionRequirements.canonical) before ∧
      ¬ SourceCurrentConjunctionRequirements.Requirements edges [] before.heap
        ((SourceCurrentConjunctionRequirements.columns edges).map SourceCurrentConjunctionRequirements.canonical) before.heap := by
  constructor
  · simp only [requirements, classes, Outcome.bind, List.append_nil]
  · have impossible : ∀ {heap rows later}, SourceCurrentConjunctionRequirements.Requirements edges [] heap rows later → False := by
      intro heap rows later actual
      cases actual with
      | run same _ => exact unequal same
    exact impossible

/-- Repeated projection jobs keep both occurrences and their exact sequential physical effects. -/
theorem repeated_jobs_keep_both_occurrences
    {forest : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before middle after : InternedConstructorTemplates.State Symbol Guard} {first second : Value Symbol Guard}
    (firstRead : SourceEqualityProjectionGraph.Forest (path.map Int.ofNat) forest before first middle)
    (secondRead : SourceEqualityProjectionGraph.Forest (path.map Int.ofNat) forest middle second after)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    StableRun (fun p h => projections p h (SourceCurrentConjunctionCompletionReads.jobs [forest] [path, path]) ⟨before, operations⟩)
      [first, second] ⟨after, operations⟩ := by
  have actual := SourceCurrentConjunctionCompletionReads.Projections.cons firstRead
    (SourceCurrentConjunctionCompletionReads.Projections.cons secondRead .nil)
  simpa only [SourceCurrentConjunctionCompletionReads.jobs, List.flatMap_cons, List.map_cons,
    List.map_nil, List.flatMap_nil, List.append_nil] using projections_complete actual operations

variable [DecidableEq Symbol]

/-- Initial invariants derive uniform execution with physical output readiness and probes. -/
theorem initial_facts_supply_uniform_worker
    (nodes : List (Value Symbol Guard)) (before : Physical Symbol Formula)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (probes : ProbeHeap before.heap) :
    ∃ rows after bound, SourceCurrentConjunctionRowsAllocation.Effects before after ∧
      SourceCurrentConjunctionRowsAllocation.RowsReady after rows ∧ ProbeHeap after.heap ∧
      ∀ fuel, bound ≤ fuel → SourceCurrentConjunctionRowsWorker.rows fuel fuel nodes before = .done rows after := by
  obtain ⟨rows, after, _, effects, rowsReady, afterProbes, stable⟩ := rows_finite nodes before ready available closed probes
  obtain ⟨bound, done⟩ := stable_uniform stable
  exact ⟨rows, after, bound, effects, rowsReady, afterProbes, done⟩

/-- A generated requirement supplies the next row worker's closed operands without a future readiness oracle. -/
theorem generated_requirement_starts_next_finite_rows
    {p h : Nat} {nodes : List (Value Symbol Guard)} {before middle : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))}
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (probes : ProbeHeap before.heap)
    (done : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done rows middle)
    {row : List (List (Value Symbol Guard))} {requirement : List (Value Symbol Guard)}
    (rowIn : row ∈ rows) (requirementIn : requirement ∈ row) :
    ∃ generated after, SourceCurrentConjunctionRowsAllocation.Effects before after ∧
      SourceCurrentConjunctionRowsAllocation.RowsReady after generated ∧ ProbeHeap after.heap ∧
      StableRun (fun p h => SourceCurrentConjunctionRowsWorker.rows p h requirement middle) generated after := by
  obtain ⟨_, firstEffects, rowsReady, middleProbes⟩ := rows_verified ready available closed probes done
  have own := rowsReady row rowIn requirement requirementIn
  obtain ⟨generated, after, _, nextEffects, nextReady, afterProbes, stable⟩ :=
    rows_finite requirement middle firstEffects.ready own.1 own.2 middleProbes
  exact ⟨generated, after, firstEffects.trans nextEffects, nextReady, afterProbes, stable⟩

/-- Whole-row success derives actual exposures and equal-arity tuples without physical input assumptions. -/
theorem raw_success_has_source_matching_tuples
    {p h : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))}
    (done : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done rows after) :
    ∃ edges heap, SourceCurrentConjunctionCompletionReads.Exposures nodes before.heap edges heap ∧
      SourceCurrentConjunctionRowsAllocation.Tuples (SourceCurrentConjunctionTuples.tuples edges)
        ⟨heap, before.equality⟩ rows after ∧
      ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, SourceCurrentConjunctionRequirements.SameArity tuple := by
  cases rows_graph done with
  | run reads allocated =>
      exact ⟨_, _, reads, allocated, fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
        (SourceCurrentConjunctionTuples.tuples_matching _ tuple member)⟩

/-- Incomparable successful bounds identify both heap and equality-operation state. -/
theorem incomparable_successes_keep_whole_physical_state
    {p h otherP otherH : Nat} {nodes : List (Value Symbol Guard)} {before after later : Physical Symbol Formula}
    {first second : List (List (List (Value Symbol Guard)))}
    (one : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done first after)
    (two : SourceCurrentConjunctionRowsWorker.rows otherP otherH nodes before = .done second later) :
    first = second ∧ after.heap = later.heap ∧ after.equality = later.equality := by
  obtain ⟨rfl, rfl⟩ := rows_done_unique one two
  exact ⟨rfl, rfl, rfl⟩

#print axioms contradiction_skips_projection_at_zero
#print axioms unequal_arity_requires_explicit_graph_scope
#print axioms repeated_jobs_keep_both_occurrences
#print axioms initial_facts_supply_uniform_worker
#print axioms generated_requirement_starts_next_finite_rows
#print axioms raw_success_has_source_matching_tuples
#print axioms incomparable_successes_keep_whole_physical_state
set_option pp.explicit true
#check @contradiction_skips_projection_at_zero
#check @unequal_arity_requires_explicit_graph_scope
#check @repeated_jobs_keep_both_occurrences
#check @initial_facts_supply_uniform_worker
#check @generated_requirement_starts_next_finite_rows
#check @raw_success_has_source_matching_tuples
#check @incomparable_successes_keep_whole_physical_state
end MicroCFTA.CurrentConjunctionRowsKernels
