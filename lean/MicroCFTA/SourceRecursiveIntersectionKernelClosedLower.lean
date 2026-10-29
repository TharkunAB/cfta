import MicroCFTA.SourceRecursiveIntersectionKernelReturnLower

/-!
# Original-input bounds for all root execution outcomes

Closed roots derive one bound before the runtime fuel and current heap.
When the constructor heap starts at the source, the bound covers every
complete Mu record in every finite execution outcome.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual row outcomes require no supplied recursive allocation theorem. -/
theorem row_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (request : EdgeRequest Symbol Guard) (scope : SourceRecursiveIntersectionCode.EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (state : Machine Symbol Guard) (valid : Valid state) (ready : EdgeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap) :
    Lower state.heap (limit + requiredFuel (view source holds) (edgeSemantic holds request) complete)
      (edge emptyGuard conjoin (execute emptyGuard conjoin fuel request.domain)
        request.left request.right state).state.heap :=
  edge_result_lower source facts limit sourceBounded holds emptyGuard conjoin fuel
    (node_lower source facts limit sourceBounded holds emptyGuard conjoin fuel)
    request scope complete state valid ready growth history semantic opened

/-- Closed original roots derive one allocation bound for every finite kernel outcome. -/
theorem closed_roots_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound, ∀ (fuel : Nat) (state : Machine Symbol Guard),
      Valid state → Grows source state.heap → Extends source.nodes.issued state.heap.nodes.issued →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      Lower state.heap bound
        (execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right state).state.heap := by
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  let limit := maximumDepth (InternedRecordCoherence.nodeInventory source) + 1
  have bounded : InternedMuDepthInventory.Bounded source limit := InternedMuDepthInventory.initial_bounded source facts
  refine ⟨limit + requiredFuel (view source holds) (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete, ?_⟩
  intro fuel state valid growth history semantic opened
  exact node_lower source facts limit bounded holds emptyGuard conjoin fuel
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ scope complete state valid
    ⟨empty_domain state, leftAvailable.grows source state.heap growth history,
      rightAvailable.grows source state.heap growth history⟩
    growth history semantic opened

/-- A source constructor heap has one body ceiling for every finite closed-root outcome. -/
theorem closed_roots_cold_bounded
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound, ∀ (fuel : Nat) (state : Machine Symbol Guard),
      state.heap = source → Valid state →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      InternedMuDepthInventory.Bounded
        (execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right state).state.heap bound := by
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  let limit := maximumDepth (InternedRecordCoherence.nodeInventory source) + 1
  let rank := requiredFuel (view source holds) (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete
  have bounded : InternedMuDepthInventory.Bounded source limit := InternedMuDepthInventory.initial_bounded source facts
  refine ⟨limit + rank, ?_⟩
  intro fuel state cold valid semantic opened
  have growth : Grows source state.heap := by rw [cold]; exact grows_refl source
  have history : Extends source.nodes.issued state.heap.nodes.issued := by rw [cold]; exact extends_refl _
  have lower := node_lower source facts limit bounded holds emptyGuard conjoin fuel
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ scope complete state valid
    ⟨empty_domain state, leftAvailable.grows source state.heap growth history,
      rightAvailable.grows source state.heap growth history⟩ growth history semantic opened
  intro key entry body depth ordinary present
  rcases lower key entry body depth ordinary present with old | small
  · rw [cold] at old
    exact Nat.lt_of_lt_of_le (bounded key entry body depth ordinary old) (Nat.le_add_right limit rank)
  · exact small

end MicroCFTA.SourceRecursiveIntersectionKernel
