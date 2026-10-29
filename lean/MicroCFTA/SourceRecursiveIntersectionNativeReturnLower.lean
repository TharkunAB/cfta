import MicroCFTA.SourceRecursiveIntersectionKernelClosedLower
import MicroCFTA.SourceRecursiveIntersectionNativeReturnDegree

/-!
# Allocation bounds at actual checked native return heaps

Exact successful native replay transfers the all-outcome kernel bound.
Closed roots derive the bound before every native return observation.
When the constructor heap starts at the source, every returned complete
Mu body has that one original-input ceiling.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView IntersectSchedule InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every new complete Mu in an actual checked native node return has the original body bound. -/
theorem node_return_lower
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
    Lower state.machine.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete) after.machine.heap := by
  obtain ⟨_afterValid, _extension, _available, bound, replay⟩ :=
    native_node_correct emptyGuard conjoin fuel request state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  have lower := SourceRecursiveIntersectionKernel.node_lower source facts limit bounded holds emptyGuard conjoin (bound + 0)
    request scope complete state.machine valid.machine ready growth history semantic opened
  simpa only [replay 0, SourceRecursiveIntersectionKernel.Result.state] using lower

/-- Every new complete Mu in an actual checked native row return has the original body bound. -/
theorem edge_return_lower
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
    Lower state.machine.heap (limit + requiredFuel (view source holds) (edgeSemantic holds request) complete) after.machine.heap := by
  obtain ⟨_afterValid, _extension, _resident, bound, replay⟩ :=
    native_edge_correct emptyGuard conjoin fuel request state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  have lower := SourceRecursiveIntersectionKernel.row_lower source facts limit bounded holds emptyGuard conjoin (bound + 0)
    request scope complete state.machine valid.machine ready growth history semantic opened
  simpa only [replay 0, SourceRecursiveIntersectionKernel.Result.state] using lower

/-- Closed roots derive one body allocation bound before all checked native node returns. -/
theorem closed_roots_return_lower
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
      ∀ value, execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after →
      Lower state.machine.heap bound after.machine.heap := by
  obtain ⟨bound, kernel⟩ := SourceRecursiveIntersectionKernel.closed_roots_lower source facts holds emptyGuard conjoin
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  refine ⟨bound, ?_⟩
  intro fuel state after valid growth history semantic opened ranges value done
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨SourceRecursiveIntersectionKernel.empty_domain state.machine,
      leftAvailable.grows source state.machine.heap growth history, rightAvailable.grows source state.machine.heap growth history⟩
  obtain ⟨_afterValid, _extension, _available, fuelBound, replay⟩ :=
    native_node_correct emptyGuard conjoin fuel ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  simpa only [replay 0, SourceRecursiveIntersectionKernel.Result.state] using
    kernel (fuelBound + 0) state.machine valid.machine growth history semantic opened

/-- A source constructor heap has one body ceiling at every checked native closed-root return. -/
theorem closed_roots_cold_return_bounded
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound, ∀ (fuel : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      state.machine.heap = source → SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state →
      SemanticHeap state.machine.heap → InternedOpenDepthReadback.Heap state.machine.heap →
      WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state →
      ∀ value, execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after →
      InternedMuDepthInventory.Bounded after.machine.heap bound := by
  obtain ⟨bound, kernel⟩ := SourceRecursiveIntersectionKernel.closed_roots_cold_bounded source facts holds emptyGuard conjoin
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  refine ⟨bound, ?_⟩
  intro fuel state after cold valid semantic opened ranges value done
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := by
    refine ⟨SourceRecursiveIntersectionKernel.empty_domain state.machine, ?_, ?_⟩
    · simpa only [cold] using leftAvailable
    · simpa only [cold] using rightAvailable
  obtain ⟨_afterValid, _extension, _available, fuelBound, replay⟩ :=
    native_node_correct emptyGuard conjoin fuel ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  simpa only [replay 0, SourceRecursiveIntersectionKernel.Result.state] using
    kernel (fuelBound + 0) state.machine cold valid.machine semantic opened

end MicroCFTA.SourceRecursiveIntersectionNative
