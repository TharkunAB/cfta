import MicroCFTA.SourceRecursiveIntersectionNativeColdEffects
import MicroCFTA.SourceRecursiveIntersectionNativeOpenDepth
import MicroCFTA.SourceFreshOrdinaryColdTable

/-!
# Finite repaired cold tables after actual native intersection

The actual first native run retains the body/probe heap. Its closed result
therefore has a finite repaired shared traversal, an exact finite map domain,
declared children, and allocation-free final-cache row replay. Checked word
ranges and original input syntax retain their stated native scope.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (CoveredRows)
open SourceFreshOrdinaryColdSharedRows (Trace ReplayedRows keys)

/-- Actual successful native execution supplies finite stable repaired tables without output preparation. -/
theorem cold_node_table [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (semantic : SemanticHeap source) (covered : Covered [] source)
    (heap : InternedOpenDepthReadback.Heap source) (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after rows final outer inner,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      Correct emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) value after (fun current value => Available current.heap value) ∧
      value.free = [] ∧ Original value ∧ Trace after.machine.heap (fun _ => none) [value] rows final ∧
      SemanticHeap final ∧ Covered [] final ∧ InternedOpenDepthReadback.Heap final ∧
      ReplayedRows final rows ∧ CoveredRows rows rows ∧ (keys final rows).Nodup ∧
      (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows) ∧
      (∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after) ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner after.machine.heap (fun _ => none) [value] = .done rows final := by
  obtain ⟨fuel, value, after, done, correct, afterSemantic, afterCovered, stable⟩ :=
    cold_node_complete source semantic covered domains domainsValid holds emptyGuard conjoin left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  have ready : NodeReady (⟨source, domains⟩ : Machine Symbol Guard) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (initial width ⟨source, domains⟩) :=
    initial_valid width emptyGuard conjoin _ ⟨semantic.1.normal.facts, domainsValid⟩
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ _ after value done
  have bounds := evaluated.bounds_of_ranges ranges
  have retained := bounds.open_depth_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid
    (semantic_requestNode _ left right _ ready) semantic (by intro value; trivial) heap
  have scope := correct.meaning.request_scope _ _ _ _ ⟨semantic.1.normal.facts, domainsValid⟩ ready semantic
  have closed := SourceRecursiveIntersectionResultScope.empty_scope value scope
  obtain ⟨rows, final, outer, inner, trace, finalSemantic, finalCovered, finalHeap, _, _, _, replayed, allChildren, distinct, domain, rowStable⟩ :=
    SourceFreshOrdinaryColdSharedRows.cold_table after.machine.heap afterSemantic afterCovered retained.2 value correct.result closed
  exact ⟨fuel, value, after, rows, final, outer, inner, done, correct, closed, correct.closed_original closed, trace,
    finalSemantic, finalCovered, finalHeap, replayed, allChildren, distinct, domain, stable, rowStable⟩

/-- Actual repaired source construction derives every heap premise for native intersection and its finite cold table. -/
theorem constructed_node_table [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (builtValue : Value Symbol Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done builtValue source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after rows final outer inner,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      Correct emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) value after (fun current value => Available current.heap value) ∧
      value.free = [] ∧ Original value ∧ Trace after.machine.heap (fun _ => none) [value] rows final ∧
      SemanticHeap final ∧ Covered [] final ∧ InternedOpenDepthReadback.Heap final ∧
      ReplayedRows final rows ∧ CoveredRows rows rows ∧ (keys final rows).Nodup ∧
      (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows) ∧
      (∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after) ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner after.machine.heap (fun _ => none) [value] = .done rows final := by
  have heap : InternedOpenDepthReadback.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  exact cold_node_table source (SourceRecursiveIntersectionSemanticHeap.constructed expression builtValue source built)
    (InternedFreshOrdinaryCoverage.closed_covered expression builtValue source built) heap domains domainsValid
    holds emptyGuard conjoin left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges

end MicroCFTA.SourceRecursiveIntersectionNative
