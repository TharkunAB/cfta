import MicroCFTA.SourceRecursiveIntersectionNativeColdProduct
import MicroCFTA.SourceSizedReferenceAPI

/-!
# Exact finite Sized classes of actual native products

Completed repaired source construction supplies every heap invariant.
Actual native intersection and cold traversal produce the table used by
the reference Sized worker. Its distinct classes contain exactly the
common input terms of each node count, with both rank inverse laws.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language RecursiveSize InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)

/-- Actual constructed native products have exact finite node-count classes, size order, and both distinct-term inverses. -/
theorem constructed_product_sized [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (builtValue : Value Symbol Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done builtValue source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ fuel value after rows final outer inner,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      Trace after.machine.heap (fun _ => none) [value] rows final ∧
      (∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after) ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner after.machine.heap (fun _ => none) [value] = .done rows final) ∧
      (let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows holds (SourceColdSharedRows.table rows (keys final rows) value))
       let classes := fun size => SourceSizedReference.classes A size (encode value)
       (∀ size, (classes size).Nodup) ∧
       (∀ size term, term ∈ classes size ↔ InternedGuardedLanguage.meaning holds ambient left term ∧
         InternedGuardedLanguage.meaning holds ambient right term ∧ nodeSize term = size) ∧
       (∀ size, SourceSizedReference.ClassEvaluation A (size + 1) size (encode value) (classes size)) ∧
       (∀ bound, (SourceSizedQueries.through classes bound).Nodup ∧
         (SourceSizedQueries.through classes bound).Pairwise (fun first second => nodeSize first ≤ nodeSize second) ∧
         ∀ term, term ∈ SourceSizedQueries.through classes bound ↔ InternedGuardedLanguage.meaning holds ambient left term ∧
           InternedGuardedLanguage.meaning holds ambient right term ∧ nodeSize term ≤ bound) ∧
       (∀ term, (∃ position, SourceSizedQueries.rank classes nodeSize term = some position) ↔
         InternedGuardedLanguage.meaning holds ambient left term ∧ InternedGuardedLanguage.meaning holds ambient right term) ∧
       (∀ term position, SourceSizedQueries.rank classes nodeSize term = some position ↔ SourceSizedQueries.unrank classes position = some term)) := by
  obtain ⟨fuel, value, after, rows, final, outer, inner, done, _, _, trace, _, _, stable, rowStable, language⟩ :=
    constructed_node_table_product expression builtValue source built domains domainsValid holds emptyGuard conjoin left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  refine ⟨fuel, value, after, rows, final, outer, inner, done, trace, stable, rowStable, ?_⟩
  dsimp only
  let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows holds (SourceColdSharedRows.table rows (keys final rows) value))
  refine ⟨(fun size => SourceSizedReference.classes_nodup A size (encode value)), ?_,
    (fun size => SourceSizedReference.classes_evaluation_bound A size (encode value)), ?_, ?_, ?_⟩
  · intro size term
    rw [SourceSizedReference.mem_classes_iff, language holds conjoined ambient term]
    exact and_assoc
  · intro bound
    refine ⟨SourceSizedReferenceAPI.through_nodup A (encode value) bound,
      SourceSizedReferenceAPI.through_ordered A (encode value) bound, ?_⟩
    intro term
    rw [SourceSizedReferenceAPI.through_exact, language holds conjoined ambient term]
    exact and_assoc
  · intro term
    rw [SourceSizedReferenceAPI.rank_exists_iff, language holds conjoined ambient term]
  · intro term position
    exact ⟨SourceSizedReferenceAPI.unrank_rank A (encode value) term position,
      SourceSizedReferenceAPI.rank_unrank A (encode value) term position⟩

end MicroCFTA.SourceRecursiveIntersectionNative
