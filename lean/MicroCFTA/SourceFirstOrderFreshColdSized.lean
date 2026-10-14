import MicroCFTA.SourceFreshOrdinaryColdSharedRows
import MicroCFTA.SourceFirstOrderColdSized

/-!
# First-order Sized laws through the actual repaired shared worklist

Actual repaired empty-cache construction supplies a prepared closed root.
The repaired shared worklist completes with the identical physical table
used by the existing exact language and Sized proofs. No warmup or supplied
trace is required. General nested shared traversal remains separate.
-/
namespace MicroCFTA.SourceFirstOrderFreshColdSized
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax)
open MergedPhysicalWarmup SourceColdSharedRows Language RecursiveSize
open SourcePreparedSharedRows (encode)

/-- Actual first-order construction and repaired cold traversal derive exact finite size classes and both inverse laws. -/
theorem source_sized [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (body : Syntax Symbol Guard) (free : InternedStoredShallowCompletion.BinderFree body)
    (meaning : Guard → Term Symbol → Bool) :
    ∃ value before rows after keys raw outer inner,
      InternedFreshOrdinaryConstruction.build (.binder smart body) [] empty = .done value before ∧
      keys.Nodup ∧ raw = table rows keys value ∧
      SourceFreshOrdinaryColdSharedRows.Trace before (fun _ => none) [value] rows after ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner before (fun _ => none) [value] = .done rows after) ∧
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
  obtain ⟨rows, after, _, _, original, _⟩ := cold_finite before facts prepared value available closed
  obtain ⟨keys, raw, _, _, distinct, rawEq, _, laws⟩ :=
    original.sized before after value rows facts prepared available closed meaning
  have inputs : Inputs before [value] := by
    intro child member
    rw [List.mem_singleton.mp member]
    exact ⟨available, closed⟩
  have trace := SourceFreshOrdinaryColdSharedRows.of_prepared original facts prepared inputs
  obtain ⟨outer, inner, done⟩ := trace.finite
  exact ⟨value, before, rows, after, keys, raw, outer, inner, built, distinct, rawEq, trace, done, laws⟩

end MicroCFTA.SourceFirstOrderFreshColdSized
