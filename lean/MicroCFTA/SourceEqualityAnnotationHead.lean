import MicroCFTA.SourceEqualityAnnotationExposure
import MicroCFTA.SourceEqualityNativeAnnotationScoped

/-!
# Physical annotations through actual complete head reads

The bounded source exposure retains annotations in every returned cache.
Literal row-node reconstruction emits no new guard. The actual head graph
therefore preserves the annotation heap without an output premise.
-/
namespace MicroCFTA.SourceEqualityAnnotationHead
open InternedConstructorTemplates InternedProbeProvenance SourceEqualityAnnotationHeap
open SourceEqualityRequiredCache SourceEqualityRequiredHead

/-- Every complete actual head read preserves physical edge annotations at its exact returned cache. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Head value before result after) (ready : Ready before) (available : Available before value)
    (closed : value.free = []) (heap : Heap annotation before) : Heap annotation after := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      have kept := SourceEqualityAnnotationExposure.nodeEdges_heap annotation fuel value before ready.semantic ready.covered heap available closed
      have middleHeap : Heap annotation middle := by simpa only [exposed, MergedSourceExposure.Result.state] using kept
      have built := SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation edges) middle middleHeap
      simpa only [rebuilt] using built

end MicroCFTA.SourceEqualityAnnotationHead
