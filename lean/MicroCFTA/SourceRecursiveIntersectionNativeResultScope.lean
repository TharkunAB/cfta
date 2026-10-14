import MicroCFTA.SourceRecursiveIntersectionKernelScope
import MicroCFTA.SourceRecursiveIntersectionNativeSuccessful

/-!
# Native recursive results have derived free-name scope

The existing guarded kernel meaning supplies an actual completed source
execution with the identical returned value and machine. Source result
scope therefore transfers to native execution. Empty-domain returns are
closed. Successful stable first execution retains that closed result.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionResultScope (Scope)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionInputView (Original)

/-- Exact guarded native request meaning derives the source result's incoming recursive pair scope. -/
theorem Meaning.request_scope [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (request : NodeRequest Symbol Guard)
    (state after : Machine Symbol Guard) (value : Value Symbol Guard)
    (meaning : Meaning emptyGuard conjoin (.node request .pure) state value after)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request) (heap : SemanticHeap state.heap) :
    Scope request.domain.key.seen value := by
  obtain ⟨fuel, repeated⟩ := meaning
  have actual := repeated 0
  change (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + 0) request.domain request.left request.right state).bind
    (fun value after => .done value after) = .done value after at actual
  rw [Nat.add_zero, result_bind_pure] at actual
  exact (SourceRecursiveIntersectionScopeCalls.execute_scoped emptyGuard conjoin fuel request.domain request.left request.right
    state valid ready.1 ready.2.1 ready.2.2 heap value after actual).2

/-- Any actual range-checked successful empty-domain native request from complete semantic heaps returns a closed value. -/
theorem done_closed_of_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (left right value : Value Symbol Guard)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (heap : SemanticHeap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state)
    (done : execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after) :
    value.free = [] := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have ready : NodeReady state.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have correct := done_correct_of_ranges emptyGuard conjoin (.node request .pure) state after value
    (fun final value => Available final.heap value) (by intro value; trivial)
    (safe_requestNode request.domain left right state.machine ready) valid ranges fuel done
  exact SourceRecursiveIntersectionResultScope.empty_scope value
    (correct.meaning.request_scope request state.machine after.machine value valid.machine ready heap)

/-- Closed original roots derive successful stable native first execution with a proved closed returned value. -/
theorem cold_node_complete_closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (heap : SemanticHeap source) (covered : Covered [] source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after, execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧ value.free = [] ∧
      ∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after := by
  obtain ⟨fuel, value, after, done, correct, semantic, payloads, stable⟩ := cold_node_complete source heap covered domains domainsValid
    holds emptyGuard conjoin left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  have ready : NodeReady (⟨source, domains⟩ : Machine Symbol Guard) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have scope := correct.meaning.request_scope _ _ _ _ ⟨heap.1.normal.facts, domainsValid⟩ ready heap
  exact ⟨fuel, value, after, done, SourceRecursiveIntersectionResultScope.empty_scope value scope, stable⟩

end MicroCFTA.SourceRecursiveIntersectionNative
