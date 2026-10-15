import MicroCFTA.SourceRecursiveIntersectionSemanticHeap
import MicroCFTA.InternedFreshOrdinaryCosts

/-!
# Cost heaps through actual intersection binders

The optional binder uses the repaired source compiler. Its execution retains
the cost heap at every outcome. The unused branch returns the current cache.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCostEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution (leaves encode leaves_available)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual optional-binder execution retains the cost heap at every outcome. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (heap : InternedFreshOrdinaryCostHeap.Heap state)
    (available : Available state body) :
    InternedFreshOrdinaryCostHeap.Heap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
  have context := SourceRecursiveIntersectionSemanticHeap.context state semantic (leaves body) (leaves_available body state available)
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body state state semantic.1.normal.facts available]
  split
  · exact (InternedFreshOrdinaryCosts.build_costs (.binder true (encode (leaves body) [.intersection pair.1 pair.2] body))
      (leaves body) state context semantic.2 heap).heap
  · exact heap

end MicroCFTA.SourceRecursiveIntersectionCostEffects
