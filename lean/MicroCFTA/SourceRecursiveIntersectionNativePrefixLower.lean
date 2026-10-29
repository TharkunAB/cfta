import MicroCFTA.SourceRecursiveIntersectionNativeNodePrefixLower
import MicroCFTA.SourceRecursiveIntersectionNativeEdgePrefixLower
import MicroCFTA.SourceRecursiveIntersectionNativeRequestPrefixLower

/-!
# Original input bounds for every finite native observation

Strong induction on the original semantic request rank closes both request kinds.
Concrete compiled branches discharge all child and body suppliers.
Every outcome retains exact old Mu records or the same original body bound.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionInputView IntersectSchedule
open InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

private theorem prefix_lower_at_rank
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (rank : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request)),
      requiredFuel (view source holds) (nodeSemantic request) complete = rank →
      ∀ (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (_valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
      (_ready : NodeReady state.machine request)
      (_growth : Grows source state.machine.heap) (_history : Extends source.nodes.issued state.machine.heap.nodes.issued)
      (_semantic : SemanticHeap state.machine.heap) (_opened : InternedOpenDepthReadback.Heap state.machine.heap)
      (_ranges : WordRanges emptyGuard conjoin (.node request .pure) state) (fuel : Nat),
      Lower state.machine.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
        (execute emptyGuard conjoin fuel (.node request .pure) state).state.machine.heap) ∧
    (∀ (request : EdgeRequest Symbol Guard) (_scope : EdgeScope source request)
      (complete : Completes (view source holds) (edgeSemantic holds request)),
      requiredFuel (view source holds) (edgeSemantic holds request) complete = rank →
      ∀ (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (_valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
      (_ready : EdgeReady state.machine request)
      (_growth : Grows source state.machine.heap) (_history : Extends source.nodes.issued state.machine.heap.nodes.issued)
      (_semantic : SemanticHeap state.machine.heap) (_opened : InternedOpenDepthReadback.Heap state.machine.heap)
      (_ranges : WordRanges emptyGuard conjoin (.edge request .pure) state) (fuel : Nat),
      Lower state.machine.heap (limit + requiredFuel (view source holds) (edgeSemantic holds request) complete)
        (execute emptyGuard conjoin fuel (.edge request .pure) state).state.machine.heap) := by
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      constructor
      · intro request scope complete same state valid ready growth history semantic opened ranges fuel
        apply node_prefix_from_body emptyGuard conjoin request state valid ready ranges
          (limit + requiredFuel (view source holds) (nodeSemantic request) complete) ?_ fuel
        intro current currentValid unchanged bodyRanges inner
        apply compiled_node_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin
          request scope complete ?_ ?_ current currentValid
          (by simpa only [unchanged] using ready) (by simpa only [unchanged] using growth)
          (by simpa only [unchanged] using history) (by simpa only [unchanged] using semantic)
          (by simpa only [unchanged] using opened) bodyRanges inner
        · intro child childScope childComplete smaller
          exact (ih (requiredFuel (view source holds) (nodeSemantic child) childComplete)
            (by rw [← same]; exact smaller)).1 child childScope childComplete rfl
        · intro child childScope childComplete smaller
          exact (ih (requiredFuel (view source holds) (edgeSemantic holds child) childComplete)
            (by rw [← same]; exact smaller)).2 child childScope childComplete rfl
      · intro request scope complete same state valid ready growth history semantic opened ranges fuel
        apply edge_prefix_from_body emptyGuard conjoin request state valid ready ranges
          (limit + requiredFuel (view source holds) (edgeSemantic holds request) complete) ?_ fuel
        intro current currentValid unchanged bodyRanges inner
        apply compiled_edge_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin
          request scope complete ?_ current currentValid
          (by simpa only [unchanged] using ready) (by simpa only [unchanged] using growth)
          (by simpa only [unchanged] using history) (by simpa only [unchanged] using semantic)
          (by simpa only [unchanged] using opened) bodyRanges inner
        · intro child childScope childComplete smaller
          exact (ih (requiredFuel (view source holds) (nodeSemantic child) childComplete)
            (by rw [← same]; exact smaller)).1 child childScope childComplete rfl

/-- Every finite native node outcome bounds new Mu bodies from its original request. -/
theorem node_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine request)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (.node request .pure) state) (fuel : Nat) :
    Lower state.machine.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
      (execute emptyGuard conjoin fuel (.node request .pure) state).state.machine.heap := by
  exact (prefix_lower_at_rank source facts limit sourceBounded holds width emptyGuard conjoin
    (requiredFuel (view source holds) (nodeSemantic request) complete)).1 request scope complete rfl
    state valid ready growth history semantic opened ranges fuel

/-- Every finite native edge outcome bounds new Mu bodies from its original request. -/
theorem edge_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : EdgeReady state.machine request)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (.edge request .pure) state) (fuel : Nat) :
    Lower state.machine.heap (limit + requiredFuel (view source holds) (edgeSemantic holds request) complete)
      (execute emptyGuard conjoin fuel (.edge request .pure) state).state.machine.heap := by
  exact (prefix_lower_at_rank source facts limit sourceBounded holds width emptyGuard conjoin
    (requiredFuel (view source holds) (edgeSemantic holds request) complete)).2 request scope complete rfl
    state valid ready growth history semantic opened ranges fuel

end MicroCFTA.SourceRecursiveIntersectionNative
