import MicroCFTA.SourceFirstOrderExposure
import MicroCFTA.SourceColdSharedRowsTermination

/-!
# Exact Sized classes from actual first-order cold construction

Repaired empty-cache construction derives the prepared closed root.
The actual cold shared walk then completes without prior warmup. Its exact
returned table has the original guarded language and all reference Sized laws.
-/
namespace MicroCFTA.SourceFirstOrderColdSized
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance
open InternedNestedConstruction (Syntax Outcome)
open MergedPhysicalWarmup SourceColdSharedRows Language RecursiveSize
open SourcePreparedSharedRows (reference encode)

/-- Actual first-order construction and cold traversal derive finite exact shared rows. -/
theorem source_rows [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : InternedStoredShallowCompletion.BinderFree body) :
    ∃ value before rows after keys raw outer inner,
      InternedFreshOrdinaryConstruction.build (.binder smart body) [] empty = .done value before ∧
      Facts before ∧ Prepared before ∧ Available before value ∧ value.free = [] ∧
      Trace before (fun _ => none) [value] rows after ∧
      Facts after ∧ Prepared after ∧ Grows before after ∧
      Cache.Extends before.nodes.issued after.nodes.issued ∧ InternedShallowHeap.NoNewMu before after ∧
      keys.Nodup ∧ (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys) ∧
      raw = table rows keys value ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner before (fun _ => none) [value] = .done rows after) ∧
      (∀ meaning term, Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)) (encode value) term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph before meaning) value term) := by
  obtain ⟨value, before, built, facts, available, prepared⟩ :=
    InternedFreshOrdinaryFirstOrderHeap.closed_prepared smart body free
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty (.binder smart body) value before built
  obtain ⟨rows, after, _, _, trace, _⟩ := cold_finite before facts prepared value available closed
  obtain ⟨keys, raw, outer, inner, distinct, domain, rawEq, done, exactLanguage⟩ :=
    trace.table_correct before after value rows facts prepared available closed
  have inputs : Inputs before [value] := by
    intro child member
    rw [List.mem_singleton.mp member]
    exact ⟨available, closed⟩
  obtain ⟨afterFacts, afterPrepared, growth, history, unchanged, _, _⟩ :=
    trace.correct facts prepared inputs (by intro _ _ impossible; cases impossible)
  exact ⟨value, before, rows, after, keys, raw, outer, inner, built, facts, prepared, available, closed,
    trace, afterFacts, afterPrepared, growth, history, unchanged, distinct, domain, rawEq, done, exactLanguage⟩

/-- No warmup or supplied trace is required for exact finite first-order cold Sized classes. -/
theorem source_sized [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (body : Syntax Symbol Guard) (free : InternedStoredShallowCompletion.BinderFree body)
    (meaning : Guard → Term Symbol → Bool) :
    ∃ value before rows after keys raw outer inner,
      InternedFreshOrdinaryConstruction.build (.binder smart body) [] empty = .done value before ∧
      keys.Nodup ∧ raw = table rows keys value ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner before (fun _ => none) [value] = .done rows after) ∧
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
  obtain ⟨value, before, built, facts, available, prepared⟩ :=
    InternedFreshOrdinaryFirstOrderHeap.closed_prepared smart body free
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty (.binder smart body) value before built
  obtain ⟨rows, after, _, _, trace, _⟩ := cold_finite before facts prepared value available closed
  obtain ⟨keys, raw, outer, inner, distinct, rawEq, done, laws⟩ :=
    trace.sized before after value rows facts prepared available closed meaning
  exact ⟨value, before, rows, after, keys, raw, outer, inner, built, distinct, rawEq, done, laws⟩

end MicroCFTA.SourceFirstOrderColdSized
