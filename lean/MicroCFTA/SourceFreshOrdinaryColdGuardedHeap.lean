import MicroCFTA.SourceFreshOrdinaryColdTable
import MicroCFTA.MergedFreshOrdinaryGuardedEffects

/-!
# Independent probe heaps at final shared cold tables

Every actual shared trace retains the independent probe-language invariant.
Closed source construction supplies its initial invariant. Existing finite
traversal bounds therefore produce final tables with this semantic evidence.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceColdSharedRows (Inputs)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedGuardedProbeHeap (Heap)

/-- An actual shared trace carries the independent probe-language heap to its exact final cache. -/
theorem Trace.guarded_heap [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : SourceColdSharedRows.Rows Symbol Guard}
    {pending : List (Value Symbol Guard)} (trace : Trace state seen pending result final)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : Heap state) (inputs : Inputs state pending) :
    Heap final := by
  induction trace with
  | nil => exact heap
  | empty rest ih | known value identity edges same present rest ih =>
      exact ih semantic covered heap (fun value member => inputs value (List.mem_cons_of_mem _ member))
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun child member => inputs child (List.mem_cons_of_mem _ member)
      have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value state semantic covered own.1 own.2
      have afterSemantic : SemanticHeap after := by simpa only [done, MergedSourceExposure.Result.state] using checked.semantic
      have afterCovered : Covered [] after := by simpa only [done, MergedSourceExposure.Result.state] using checked.covered
      have afterHeap : Heap after := by
        simpa only [done, MergedSourceExposure.Result.state] using
          MergedFreshOrdinaryGuardedEffects.nodeEdges_heap fuel value state semantic covered heap own.1 own.2
      have growth : Grows state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
      have history : Extends state.nodes.issued after.nodes.issued := by
        simpa only [done, MergedSourceExposure.Result.state] using checked.history
      have edgeResident := checked.edges edges after done
      have edgeClosed := checked.closed edges after done
      apply ih afterSemantic afterCovered afterHeap
      intro child member
      rcases List.mem_append.mp member with first | later
      · obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp first
        exact ⟨afterSemantic.1.normal.facts.cached.edges edge.entry.key edge (edgeResident edge edgeIn) child childIn,
          edgeClosed edge edgeIn child childIn⟩
      · exact ⟨(tail child later).1.grows state after growth history, (tail child later).2⟩

/-- Finite actual shared traversal retains both depth and independent-language probe heaps. -/
theorem cold_finite_guarded [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (depthHeap : InternedOpenDepthReadback.Heap state)
    (heap : Heap state) (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) :
    ∃ rows after outer inner, Trace state (fun _ => none) [value] rows after ∧
      InternedOpenDepthReadback.Heap after ∧ Heap after ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner state (fun _ => none) [value] = .done rows after := by
  obtain ⟨rows, after, outer, inner, trace, afterDepth, stable⟩ :=
    SourceFreshOrdinaryColdSharedTermination.cold_finite state semantic covered depthHeap value available closed
  exact ⟨rows, after, outer, inner, trace, afterDepth,
    trace.guarded_heap semantic covered heap
      (by intro child member; simpa only [List.mem_singleton.mp member] using And.intro available closed), stable⟩

/-- Actual completed closed construction supplies every premise of the finite traversal and its final semantic heap. -/
theorem constructed_cold_finite_guarded [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) :
    ∃ rows after outer inner, Trace state (fun _ => none) [value] rows after ∧
      InternedOpenDepthReadback.Heap after ∧ Heap after ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner state (fun _ => none) [value] = .done rows after := by
  have heap : Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  have depthHeap : InternedOpenDepthReadback.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  exact cold_finite_guarded state (SourceRecursiveIntersectionSemanticHeap.constructed expression value state built)
    (InternedFreshOrdinaryCoverage.closed_covered expression value state built) depthHeap heap value
    ((InternedFreshOrdinaryFacts.closed_verified expression).result value state built)
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built)

end MicroCFTA.SourceFreshOrdinaryColdSharedRows
