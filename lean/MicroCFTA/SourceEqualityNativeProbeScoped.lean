import MicroCFTA.SourceRecursiveIntersectionNativeProbeHeap
import MicroCFTA.SourceEqualityNativeScoped
import MicroCFTA.SourceEqualityClassFoldGraph

/-!
# Filtered Mu probes through scoped native equality requests

The actual evaluation supplies its checked word bounds. Compiled source
calls retain both probe filters through their returned warm native state.
No output probe invariant is supplied.
-/
namespace MicroCFTA.SourceEqualityNativeProbeScoped
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedFreshOrdinaryProbeHeap (Heap)

/-- Each completed scoped native request preserves filtered Mu probes through actual compiled calls. -/
theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (trace : Step emptyGuard conjoin target input before result after) (ready : IdleReady emptyGuard conjoin before)
    (targetAvailable : Available before.machine.heap target) (inputAvailable : Available before.machine.heap input)
    (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | done fuel ranges actual =>
      have nodeReady : NodeReady before.machine ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ :=
        ⟨empty_domain _, targetAvailable, inputAvailable⟩
      have evaluated := SourceRecursiveIntersectionNative.evaluation_of_done emptyGuard conjoin fuel _ before after result actual
      have bounds := evaluated.bounds_of_ranges ranges
      exact (bounds.filtered_probe_heaps (fun current value => Available current.heap value)
        (by intro value; trivial) (safe_requestNode _ _ _ _ nodeReady) ready.valid
        (semantic_requestNode _ _ _ _ nodeReady) ready.semantic.ready.semantic (by intro value; trivial) heap).2

end MicroCFTA.SourceEqualityNativeProbeScoped
