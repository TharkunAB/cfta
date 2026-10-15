import MicroCFTA.SourceEqualityNativeScoped
import MicroCFTA.SourceRecursiveIntersectionNativeCostHeap

/-!
# Cost heaps through scoped native requests

The proof uses the actual completed request and its word checks. Current
operand availability supplies the compiled call premises. The operands need
not be closed for cost-heap preservation. Completion remains a premise.
-/
namespace MicroCFTA.SourceEqualityNativeScoped
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- An actual completed scoped request retains the current cost heap. -/
theorem Step.cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Step emptyGuard conjoin target input before result after) (ready : IdleReady emptyGuard conjoin before)
    (costHeap : InternedFreshOrdinaryCostHeap.Heap before.machine.heap)
    (targetAvailable : Available before.machine.heap target) (inputAvailable : Available before.machine.heap input) :
    InternedFreshOrdinaryCostHeap.Heap after.machine.heap := by
  cases trace with
  | done fuel ranges actual =>
      have nodeReady : NodeReady before.machine ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ :=
        ⟨empty_domain _, targetAvailable, inputAvailable⟩
      exact SourceRecursiveIntersectionNative.done_cost_heap_of_ranges emptyGuard conjoin _ before after result
        (fun current value => Available current.heap value) (by intro value; trivial)
        (safe_requestNode _ _ _ _ nodeReady) ready.valid
        (semantic_requestNode _ _ _ _ nodeReady) ready.semantic.ready.semantic
        (by intro value; trivial) costHeap ranges fuel actual

end MicroCFTA.SourceEqualityNativeScoped
