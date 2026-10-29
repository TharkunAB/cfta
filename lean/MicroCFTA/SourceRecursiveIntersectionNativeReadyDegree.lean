import MicroCFTA.SourceRecursiveIntersectionKernelClosedDegree
import MicroCFTA.SourceRecursiveIntersectionNativeSourceCalls

/-!
# Original-input degree bounds at actual completed native memo hits

Actual lookup and demand supply the existing guarded kernel replay.
The closed kernel theorem bounds that exact cached value.
No separate cached-value degree provenance is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView IntersectSchedule InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual ready node hits derive the same original-request degree bound. -/
theorem node_ready_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (bounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (handle : Nat) (value : Value Symbol Guard)
    (lookup : lookupNode width request state = (.memoized handle, selected))
    (demand : demandNode handle selected = (.ready value, current)) :
    SemanticHeap current.machine.heap ∧ InternedOpenDepthReadback.Heap current.machine.heap ∧
      valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete := by
  obtain ⟨_currentValid, _sameMachine, _available, fuel, replay⟩ :=
    node_ready_source emptyGuard conjoin state selected current valid request ready safe handle value lookup demand
  exact SourceRecursiveIntersectionKernel.node_result_degree source facts limit bounded holds emptyGuard conjoin (fuel + 0)
    request scope complete state.machine current.machine valid.machine ready growth history semantic opened value (replay 0)

/-- Actual ready edge hits derive the same original-row degree bound. -/
theorem edge_ready_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (bounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (request : EdgeRequest Symbol Guard) (scope : SourceRecursiveIntersectionCode.EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (handle : Nat) (value : EdgeValue Symbol Guard)
    (lookup : lookupEdge width request state = (handle, selected))
    (demand : demandEdge handle selected = (.ready value, current)) :
    SemanticHeap current.machine.heap ∧ InternedOpenDepthReadback.Heap current.machine.heap ∧
      manyDepth value.children ≤ limit + requiredFuel (view source holds) (edgeSemantic holds request) complete := by
  obtain ⟨_currentValid, _sameMachine, _resident, fuel, replay⟩ :=
    edge_ready_source emptyGuard conjoin state selected current valid request ready safe handle value lookup demand
  exact SourceRecursiveIntersectionKernel.row_result_degree source facts limit bounded holds emptyGuard conjoin (fuel + 0)
    request scope complete state.machine current.machine valid.machine ready growth history semantic opened value (replay 0)

end MicroCFTA.SourceRecursiveIntersectionNative
