import MicroCFTA.SourceRecursiveIntersectionNativeReturnDegree

/-!
# Actual completed native child facts for prefix proofs

The literal child return derives strong memo validity and physical growth.
The same observation supplies both heap invariants and the original degree.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView IntersectSchedule InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- A completed checked node child supplies all facts at its exact returned state. -/
theorem node_return_degree_facts
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
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after ∧
      SourceRecursiveIntersectionKernel.Extension state.machine after.machine ∧ Available after.machine.heap value ∧
      SemanticHeap after.machine.heap ∧ InternedOpenDepthReadback.Heap after.machine.heap ∧
      valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete := by
  obtain ⟨afterValid, extension, available, _bound, _replay⟩ :=
    native_node_correct emptyGuard conjoin fuel request state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  obtain ⟨afterSemantic, afterOpened, degree⟩ := node_return_degree source facts limit bounded holds width
    emptyGuard conjoin fuel request scope complete state after valid ready growth history semantic opened ranges value done
  exact ⟨afterValid, extension, available, afterSemantic, afterOpened, degree⟩

/-- A completed checked row child supplies all facts at its exact returned state. -/
theorem edge_return_degree_facts
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
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after ∧
      SourceRecursiveIntersectionKernel.Extension state.machine after.machine ∧ EdgeResident after.machine.heap value ∧
      SemanticHeap after.machine.heap ∧ InternedOpenDepthReadback.Heap after.machine.heap ∧
      manyDepth value.children ≤ limit + requiredFuel (view source holds) (edgeSemantic holds request) complete := by
  obtain ⟨afterValid, extension, resident, _bound, _replay⟩ :=
    native_edge_correct emptyGuard conjoin fuel request state after value valid ready done
      ((evaluation_of_done emptyGuard conjoin fuel _ state after value done).bounds_of_ranges ranges)
  obtain ⟨afterSemantic, afterOpened, degree⟩ := edge_return_degree source facts limit bounded holds width
    emptyGuard conjoin fuel request scope complete state after valid ready growth history semantic opened ranges value done
  exact ⟨afterValid, extension, resident, afterSemantic, afterOpened, degree⟩

end MicroCFTA.SourceRecursiveIntersectionNative
