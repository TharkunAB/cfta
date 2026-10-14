import MicroCFTA.SourceFreshOrdinaryColdGuardedExact
import MicroCFTA.SourceSizedReferenceAPI

/-!
# Exact Sized classes from general repaired closed construction

Completed empty-cache construction supplies the complete semantic heaps.
The actual cold traversal produces a finite ascending table. Its independent
guarded language determines exact distinct node-count classes, finite class
execution, size order, and both rank inverse laws.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSized
open Cache Language RecursiveSize InternedConstructorTemplates InternedProbeProvenance
open SourcePreparedSharedRows (encode)
open SourceFreshOrdinaryColdSharedRows (keys)

/-- General completed repaired construction has exact finite cold Sized classes without preparation or a supplied trace. -/
theorem source_sized [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (value : Value Symbol Guard) (state : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ rows final keys raw outer inner,
      keys.Nodup ∧ raw = SourceColdSharedRows.table rows keys value ∧
      SourceFreshOrdinaryColdSharedRows.Trace state (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner state (fun _ => none) [value] = .done rows final) ∧
      (let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows holds raw)
       let classes := fun size => SourceSizedReference.classes A size (encode value)
       (∀ size term, term ∈ classes size ↔ InternedGuardedLanguage.meaning holds ambient value term ∧ nodeSize term = size) ∧
       (∀ size, SourceSizedReference.ClassEvaluation A (size + 1) size (encode value) (classes size)) ∧
       (∀ bound, (SourceSizedQueries.through classes bound).Nodup ∧
         (SourceSizedQueries.through classes bound).Pairwise (fun first second => nodeSize first ≤ nodeSize second) ∧
         ∀ term, term ∈ SourceSizedQueries.through classes bound ↔
           InternedGuardedLanguage.meaning holds ambient value term ∧ nodeSize term ≤ bound) ∧
       (∀ term position, SourceSizedQueries.rank classes nodeSize term = some position ↔
         SourceSizedQueries.unrank classes position = some term)) := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression value state built
  have covered := InternedFreshOrdinaryCoverage.closed_covered expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  have heap : InternedOpenDepthReadback.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  have guarded : InternedGuardedProbeHeap.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  have budgetHeap : InternedGuardedBudgetProbeHeap.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedBudgetExecution.closed_heap expression
  obtain ⟨rows, final, outer, inner, trace, _, _, _, _, _, _, _, _, distinct, domain, stable⟩ :=
    SourceFreshOrdinaryColdSharedRows.cold_table state semantic covered heap value available closed
  let raw := SourceColdSharedRows.table rows (keys final rows) value
  have exactLanguage := SourceFreshOrdinaryColdGuardedExact.trace_table_exact state final value rows trace semantic covered
    guarded budgetHeap available closed (keys final rows) domain holds ambient
  refine ⟨rows, final, keys final rows, raw, outer, inner, distinct, rfl, trace, stable, ?_⟩
  dsimp only
  let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows holds raw)
  refine ⟨?_, (fun size => SourceSizedReference.classes_evaluation_bound A size (encode value)), ?_, ?_⟩
  · intro size term
    rw [SourceSizedReference.mem_classes_iff, exactLanguage term]
  · intro bound
    refine ⟨SourceSizedReferenceAPI.through_nodup A (encode value) bound,
      SourceSizedReferenceAPI.through_ordered A (encode value) bound, ?_⟩
    intro term
    rw [SourceSizedReferenceAPI.through_exact, exactLanguage term]
  · intro term position
    exact ⟨SourceSizedReferenceAPI.unrank_rank A (encode value) term position,
      SourceSizedReferenceAPI.rank_unrank A (encode value) term position⟩

end MicroCFTA.SourceFreshOrdinaryColdSized
