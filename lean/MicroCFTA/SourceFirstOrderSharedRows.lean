import MicroCFTA.SourceFirstOrderExposure
import MicroCFTA.SourcePreparedSharedRowsLanguage
import MicroCFTA.SourceSizedReferenceAPI

/-!
# Source-derived first-order shared rows and exact size classes

Repaired empty-cache construction supplies a closed prepared root. Finite
warmup supplies a fixed cache for exact shared row reads. The resulting
finite table has the original guarded language, exact node-count classes,
finite class evaluations, size-order prefixes, and both inverse laws.

Warmup is an explicit proof construction. This theorem does not identify its
allocation order with the native cold shared traversal.
-/
namespace MicroCFTA.SourceFirstOrderSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedRecordCoherence
open InternedNestedProvenance
open InternedNestedConstruction (Syntax Outcome)
open MergedPhysicalWarmup MergedPhysicalMergeContext SourcePreparedSharedRows
open Language RecursiveSize

/-- Actual first-order construction and finite warmup supply exact guarded shared rows. -/
theorem source_rows [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : InternedStoredShallowCompletion.BinderFree body) :
    ∃ value before outputs view, ∃ (context : Context view outputs) (prepared : Prepared view), ∃ fuel raw,
      InternedFreshOrdinaryConstruction.build (.binder smart body) [] empty = .done value before ∧
      Facts before ∧ Prepared before ∧ Available before value ∧ value.free = [] ∧
      warmup (nodeInventory before) before = .done outputs view ∧
      Grows before view ∧ Cache.Extends before.nodes.issued view.nodes.issued ∧
      InternedShallowHeap.NoNewMu before view ∧
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap view outputs context prepared)
        larger (reference value) = some raw) ∧
      (∀ meaning term, Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)) (encode value) term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph before meaning) value term) := by
  obtain ⟨value, before, built, facts, available, prepared⟩ :=
    InternedFreshOrdinaryFirstOrderHeap.closed_prepared smart body free
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty (.binder smart body) value before built
  obtain ⟨outputs, view, warmed, viewFacts, growth, history, unchanged, retained, ready⟩ := prepare before facts prepared
  let context : Context view outputs := ⟨viewFacts, retained, ready⟩
  have preparedView := prepared.preserve unchanged
  have input := available.grows before view growth history
  obtain ⟨fuel, raw, read⟩ := toRows_finite view outputs context preparedView value input
  refine ⟨value, before, outputs, view, context, preparedView, fuel, raw,
    built, facts, prepared, available, closed, warmed, growth, history, unchanged, read, ?_⟩
  intro meaning term
  exact (toRows_language view outputs context preparedView value input closed fuel raw (read fuel (Nat.le_refl _))
    meaning term).trans
    (MergedColdGraphTransport.accepts_stable before view facts viewFacts prepared growth history meaning value available term).symm

/-- Source-derived recursive tables have finite exact distinct classes and both rank inverses. -/
theorem source_sized [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (body : Syntax Symbol Guard) (free : InternedStoredShallowCompletion.BinderFree body)
    (meaning : Guard → Term Symbol → Bool) :
    ∃ value before outputs view, ∃ (context : Context view outputs) (prepared : Prepared view), ∃ fuel raw,
      InternedFreshOrdinaryConstruction.build (.binder smart body) [] empty = .done value before ∧
      warmup (nodeInventory before) before = .done outputs view ∧
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap view outputs context prepared)
        larger (reference value) = some raw) ∧
      (let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)
       let classes := fun size => SourceSizedReference.classes A size (encode value)
       (∀ size term, term ∈ classes size ↔
         EpsilonUnion.Accepts (MergedPhysicalLanguage.graph before meaning) value term ∧ nodeSize term = size) ∧
       (∀ size, SourceSizedReference.ClassEvaluation A (size + 1) size (encode value) (classes size)) ∧
       (∀ bound, (SourceSizedQueries.through classes bound).Nodup ∧
         (SourceSizedQueries.through classes bound).Pairwise (fun first second => nodeSize first ≤ nodeSize second) ∧
         ∀ term, term ∈ SourceSizedQueries.through classes bound ↔
           EpsilonUnion.Accepts (MergedPhysicalLanguage.graph before meaning) value term ∧ nodeSize term ≤ bound) ∧
       (∀ term position, SourceSizedQueries.rank classes nodeSize term = some position ↔
         SourceSizedQueries.unrank classes position = some term)) := by
  obtain ⟨value, before, outputs, view, context, prepared, fuel, raw, built, _, _, _, _, warmed,
    _, _, _, read, exactLanguage⟩ := source_rows smart body free
  refine ⟨value, before, outputs, view, context, prepared, fuel, raw, built, warmed, read, ?_⟩
  dsimp only
  let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)
  refine ⟨?_, (fun size => SourceSizedReference.classes_evaluation_bound A size (encode value)), ?_, ?_⟩
  · intro size term
    rw [SourceSizedReference.mem_classes_iff, exactLanguage meaning term]
  · intro bound
    refine ⟨SourceSizedReferenceAPI.through_nodup A (encode value) bound,
      SourceSizedReferenceAPI.through_ordered A (encode value) bound, ?_⟩
    intro term
    rw [SourceSizedReferenceAPI.through_exact, exactLanguage meaning term]
  · intro term position
    exact ⟨SourceSizedReferenceAPI.unrank_rank A (encode value) term position,
      SourceSizedReferenceAPI.rank_unrank A (encode value) term position⟩

end MicroCFTA.SourceFirstOrderSharedRows
