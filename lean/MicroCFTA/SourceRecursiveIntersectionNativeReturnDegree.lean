import MicroCFTA.SourceRecursiveIntersectionNativeReadyDegree
import MicroCFTA.SourceRecursiveIntersectionNativeApi
import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate

/-!
# Original-input degree bounds for actual native returns

Existing checked-word correspondence supplies the exact kernel execution.
The closed degree theorem bounds the same native value and returned heap.
Closed original roots derive one bound before any native execution.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView IntersectSchedule InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- A checked actual native node return has the original request's degree bound. -/
theorem node_return_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (bounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine request)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (.node request .pure) state)
    (value : Value Symbol Guard)
    (done : execute emptyGuard conjoin fuel (.node request .pure) state = .done value after) :
    SemanticHeap after.machine.heap ∧ InternedOpenDepthReadback.Heap after.machine.heap ∧
      valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete := by
  obtain ⟨_afterValid, _extension, _available, bound, replay⟩ :=
    native_node_correct emptyGuard conjoin fuel request state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  exact SourceRecursiveIntersectionKernel.node_result_degree source facts limit bounded holds emptyGuard conjoin (bound + 0)
    request scope complete state.machine after.machine valid.machine ready growth history semantic opened value (replay 0)

/-- A checked actual native row return has the original row's degree bound. -/
theorem edge_return_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (bounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (request : EdgeRequest Symbol Guard) (scope : SourceRecursiveIntersectionCode.EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : EdgeReady state.machine request)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (.edge request .pure) state)
    (value : EdgeValue Symbol Guard)
    (done : execute emptyGuard conjoin fuel (.edge request .pure) state = .done value after) :
    SemanticHeap after.machine.heap ∧ InternedOpenDepthReadback.Heap after.machine.heap ∧
      manyDepth value.children ≤ limit + requiredFuel (view source holds) (edgeSemantic holds request) complete := by
  obtain ⟨_afterValid, _extension, _resident, bound, replay⟩ :=
    native_edge_correct emptyGuard conjoin fuel request state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  exact SourceRecursiveIntersectionKernel.row_result_degree source facts limit bounded holds emptyGuard conjoin (bound + 0)
    request scope complete state.machine after.machine valid.machine ready growth history semantic opened value (replay 0)

/-- Closed original roots derive one finite degree bound for all checked actual native returns. -/
theorem closed_roots_return_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound, ∀ (fuel : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state →
      Grows source state.machine.heap → Extends source.nodes.issued state.machine.heap.nodes.issued →
      SemanticHeap state.machine.heap → InternedOpenDepthReadback.Heap state.machine.heap →
      WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state →
      ∀ value, execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        state = .done value after →
      SemanticHeap after.machine.heap ∧ InternedOpenDepthReadback.Heap after.machine.heap ∧ valueDepth value ≤ bound := by
  obtain ⟨bound, bounded⟩ := SourceRecursiveIntersectionKernel.closed_roots_degree source facts holds emptyGuard conjoin
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  refine ⟨bound, ?_⟩
  intro fuel state after valid growth history semantic opened ranges value done
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨SourceRecursiveIntersectionKernel.empty_domain state.machine,
      leftAvailable.grows source state.machine.heap growth history, rightAvailable.grows source state.machine.heap growth history⟩
  obtain ⟨_afterValid, _extension, _available, kernelFuel, replay⟩ :=
    native_node_correct emptyGuard conjoin fuel _ state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  exact bounded (kernelFuel + 0) state.machine after.machine valid.machine growth history semantic opened value (replay 0)

end MicroCFTA.SourceRecursiveIntersectionNative
