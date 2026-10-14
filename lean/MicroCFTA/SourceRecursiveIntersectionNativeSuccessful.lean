import MicroCFTA.SourceRecursiveIntersectionNativeNoConstructor
import MicroCFTA.SourceRecursiveIntersectionNativeColdObservation

/-!
# Successful first native execution for closed original inputs

The existing finite bound reaches a return or a pending constructor.
Complete semantic heaps exclude pending construction along the actual run.
The returned value and cache therefore have finite native execution,
checked guarded source meaning, and retained semantic heaps and coverage.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Closed original roots derive successful first native execution from complete semantic caches and checked words. -/
theorem cold_node_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (semantic : SemanticHeap source) (covered : Covered [] source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      Correct emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) value after (fun final value => Available final.heap value) ∧
      SemanticHeap after.machine.heap ∧ Covered [] after.machine.heap ∧
      ∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after := by
  have facts := semantic.1.normal.facts
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  let start := initial width (⟨source, domains⟩ : Machine Symbol Guard)
  have valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin start :=
    initial_valid width emptyGuard conjoin _ ⟨facts, domainsValid⟩
  have ready : NodeReady start.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have safe := safe_requestNode request.domain left right start.machine ready
  have certificate := semantic_requestNode request.domain left right start.machine ready
  have clean : BodyCode (Code.node request Code.pure) := by intro value; trivial
  obtain ⟨fuel, terminal⟩ := cold_node_terminal source facts domains domainsValid holds emptyGuard conjoin left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  generalize observed : execute emptyGuard conjoin fuel (.node request .pure) start = outcome at terminal
  cases terminal with
  | done value after =>
      have evaluated := evaluation_of_done emptyGuard conjoin fuel (.node request .pure) start after value observed
      have bounds := evaluated.bounds_of_ranges ranges
      have complete := bounds.correct (fun final value => Available final.heap value) clean safe valid
      have returned := bounds.semantic_heap (fun final value => Available final.heap value) clean safe valid certificate semantic
      obtain ⟨steps, _, trace⟩ := done_trace emptyGuard conjoin fuel (.node request .pure) start after value observed
      have payloads := trace.covered emptyGuard conjoin steps _ _ start after facts.coherent.valid covered
      exact ⟨fuel, value, after, observed, complete, returned, payloads.2,
        fun extra => done_stable emptyGuard conjoin fuel extra _ start after value observed⟩
  | constructor key remaining after =>
      exact False.elim (no_constructor emptyGuard conjoin fuel (.node request .pure) start after key remaining
        (fun final value => Available final.heap value) clean safe valid certificate semantic covered ranges observed)

/-- Actual closed source construction supplies successful stable native first execution without semantic-heap premises. -/
theorem constructed_node_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    ∃ fuel value after,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      ∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after := by
  obtain ⟨fuel, value, after, done, _, _, _, stable⟩ := cold_node_complete source
    (SourceRecursiveIntersectionSemanticHeap.constructed expression builtValue source built)
    (InternedFreshOrdinaryCoverage.closed_covered expression builtValue source built)
    domains domainsValid holds emptyGuard conjoin left right leftOriginal rightOriginal leftAvailable rightAvailable
    leftClosed rightClosed ranges
  exact ⟨fuel, value, after, done, stable⟩

end MicroCFTA.SourceRecursiveIntersectionNative
