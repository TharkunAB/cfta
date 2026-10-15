import MicroCFTA.SourceEqualityProbeExposure
import MicroCFTA.SourceEqualityNativeProbeScoped

/-!
# Filtered Mu probes through actual complete head reads

The bounded source exposure retains filtered probes in every returned cache.
Literal row-node reconstruction adds no Mu. The actual head graph
therefore preserves the probe invariant without an output premise.
-/
namespace MicroCFTA.SourceEqualityProbeHead
open InternedConstructorTemplates InternedProbeProvenance InternedFreshOrdinaryProbeHeap
open SourceEqualityRequiredCache SourceEqualityRequiredHead

/-- Every complete actual head read preserves both Mu probe filters at its exact returned cache. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Head value before result after) (ready : Ready before) (available : Available before value)
    (closed : value.free = []) (heap : Heap before) : Heap after := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      have kept := SourceEqualityProbeExposure.nodeEdges_heap fuel value before ready.semantic ready.covered heap available closed
      have middleHeap : Heap middle := by simpa only [exposed, MergedSourceExposure.Result.state] using kept
      have built := InternedFreshOrdinaryProbeHeap.node edges middle middleHeap
      simpa only [rebuilt] using built

end MicroCFTA.SourceEqualityProbeHead
