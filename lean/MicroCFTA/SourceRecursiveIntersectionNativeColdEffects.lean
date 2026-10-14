import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.MergedFreshOrdinaryColdEffects

/-!
# General cold-reader effects after actual native intersection

Successful first native execution derives a closed original result in its
exact returned cache. Every bounded repaired cold read of that result keeps
complete semantic heaps and coverage. No output preparation premise is used.
Finite completion of repeated reads and product language remain open.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual first native execution supplies the full general repaired cold-reader invariant at every bound. -/
theorem cold_node_read_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (semantic : SemanticHeap source) (covered : Covered [] source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after, execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      value.free = [] ∧ Original value ∧
      (∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after) ∧
      ∀ bound, MergedFreshOrdinaryColdEffects.Verified after.machine.heap
        (MergedFreshOrdinaryExposure.nodeEdges bound value after.machine.heap) := by
  obtain ⟨fuel, value, after, done, correct, finalSemantic, finalCovered, stable⟩ :=
    cold_node_complete source semantic covered domains domainsValid holds emptyGuard conjoin left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  have ready : NodeReady (⟨source, domains⟩ : Machine Symbol Guard) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have scope := correct.meaning.request_scope _ _ _ _ ⟨semantic.1.normal.facts, domainsValid⟩ ready semantic
  have closed := SourceRecursiveIntersectionResultScope.empty_scope value scope
  exact ⟨fuel, value, after, done, closed, correct.closed_original closed, stable,
    fun bound => MergedFreshOrdinaryColdEffects.nodeEdges_verified bound value after.machine.heap
      finalSemantic finalCovered correct.result closed⟩

end MicroCFTA.SourceRecursiveIntersectionNative
