import MicroCFTA.SourceRecursiveIntersectionKernelReturnDegree

/-!
# Closed original-input degree bounds for actual kernel returns

The row theorem discharges the smaller-runtime hypothesis.
Closed original roots derive their semantic certificate and source ceiling.
One original-input bound applies to every successful runtime-fuel observation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual original row returns have a bound with no supplied child-return theorem. -/
theorem row_result_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (request : EdgeRequest Symbol Guard) (scope : SourceRecursiveIntersectionCode.EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (state after : Machine Symbol Guard) (valid : Valid state) (ready : EdgeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap)
    (value : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (execute emptyGuard conjoin fuel request.domain)
      request.left request.right state = .done value after) :
    SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
      manyDepth value.children ≤ limit + requiredFuel (view source holds) (edgeSemantic holds request) complete :=
  edge_result_degree source facts holds emptyGuard conjoin limit fuel
    (node_result_degree source facts limit sourceBounded holds emptyGuard conjoin fuel)
    request scope complete state after valid ready growth history semantic opened value done

/-- Closed original roots derive one finite degree bound for every actual successful return. -/
theorem closed_roots_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound, ∀ (fuel : Nat) (state after : Machine Symbol Guard),
      Valid state → Grows source state.heap → Extends source.nodes.issued state.heap.nodes.issued →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      ∀ value, execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right state = .done value after →
      SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧ valueDepth value ≤ bound := by
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  let limit := maximumDepth (InternedRecordCoherence.nodeInventory source) + 1
  have bounded : InternedMuDepthInventory.Bounded source limit := InternedMuDepthInventory.initial_bounded source facts
  refine ⟨limit + requiredFuel (view source holds) (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete, ?_⟩
  intro fuel state after valid growth history semantic opened value done
  exact node_result_degree source facts limit bounded holds emptyGuard conjoin fuel
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ scope complete state after valid
    ⟨empty_domain state, leftAvailable.grows source state.heap growth history,
      rightAvailable.grows source state.heap growth history⟩
    growth history semantic opened value done

end MicroCFTA.SourceRecursiveIntersectionKernel
