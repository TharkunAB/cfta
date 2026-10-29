import MicroCFTA.SourceRecursiveIntersectionNativePrefixLower

/-!
# Original closed-root bounds at every native observation

The source inventory and original semantic completion select one body bound.
The bound precedes all runtime fuel and later constructor heaps.
A source constructor heap gives the same bound for every complete Mu body.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionCode IntersectSchedule
open InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Closed original roots derive one allocation bound for every finite native outcome. -/
theorem closed_roots_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound, ∀ (fuel : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state →
      Grows source state.machine.heap → Extends source.nodes.issued state.machine.heap.nodes.issued →
      SemanticHeap state.machine.heap → InternedOpenDepthReadback.Heap state.machine.heap →
      WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state →
      Lower state.machine.heap bound
        (execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state).state.machine.heap := by
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  let limit := maximumDepth (InternedRecordCoherence.nodeInventory source) + 1
  have bounded : InternedMuDepthInventory.Bounded source limit := InternedMuDepthInventory.initial_bounded source facts
  refine ⟨limit + requiredFuel (view source holds) (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete, ?_⟩
  intro fuel state valid growth history semantic opened ranges
  exact node_prefix_lower source facts limit bounded holds width emptyGuard conjoin
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ scope complete state valid
    ⟨SourceRecursiveIntersectionKernel.empty_domain state.machine,
      leftAvailable.grows source state.machine.heap growth history,
      rightAvailable.grows source state.machine.heap growth history⟩
    growth history semantic opened ranges fuel

/-- A source constructor heap has one body ceiling at every finite native closed-root observation. -/
theorem closed_roots_cold_prefix_bounded
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound, ∀ (fuel : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      state.machine.heap = source → SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state →
      SemanticHeap state.machine.heap → InternedOpenDepthReadback.Heap state.machine.heap →
      WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state →
      InternedMuDepthInventory.Bounded
        (execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state).state.machine.heap bound := by
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  let limit := maximumDepth (InternedRecordCoherence.nodeInventory source) + 1
  let rank := requiredFuel (view source holds) (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete
  have bounded : InternedMuDepthInventory.Bounded source limit := InternedMuDepthInventory.initial_bounded source facts
  refine ⟨limit + rank, ?_⟩
  intro fuel state cold valid semantic opened ranges
  have growth : Grows source state.machine.heap := by rw [cold]; exact grows_refl source
  have history : Extends source.nodes.issued state.machine.heap.nodes.issued := by rw [cold]; exact extends_refl _
  have lower := node_prefix_lower source facts limit bounded holds width emptyGuard conjoin
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ scope complete state valid
    ⟨SourceRecursiveIntersectionKernel.empty_domain state.machine,
      leftAvailable.grows source state.machine.heap growth history,
      rightAvailable.grows source state.machine.heap growth history⟩ growth history semantic opened ranges fuel
  intro key entry body depth ordinary present
  rcases lower key entry body depth ordinary present with old | small
  · rw [cold] at old
    exact Nat.lt_of_lt_of_le (bounded key entry body depth ordinary old) (Nat.le_add_right limit rank)
  · exact small

end MicroCFTA.SourceRecursiveIntersectionNative
