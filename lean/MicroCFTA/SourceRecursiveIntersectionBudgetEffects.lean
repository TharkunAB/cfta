import MicroCFTA.SourceRecursiveIntersectionSemanticHeap
import MicroCFTA.InternedGuardedBudgetStoredExecution

/-!
# Budget heaps through actual intersection binders

An optional binder uses the actual repaired source compiler. Its complete
execution proof retains the budget probe heap. The unused branch returns
the current body and cache.
-/
namespace MicroCFTA.SourceRecursiveIntersectionBudgetEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution (leaves encode leaves_available)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual optional-binder execution retains the complete budget probe heap at every outcome. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (heap : InternedGuardedBudgetProbeHeap.Heap state)
    (available : Available state body) :
    InternedGuardedBudgetProbeHeap.Heap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
  have context := SourceRecursiveIntersectionSemanticHeap.context state semantic (leaves body) (leaves_available body state available)
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body state state semantic.1.normal.facts available]
  split
  · exact (InternedGuardedBudgetExecution.build_language (.binder true (encode (leaves body) [.intersection pair.1 pair.2] body))
      (leaves body) state context heap semantic.2).heap
  · exact heap

end MicroCFTA.SourceRecursiveIntersectionBudgetEffects
