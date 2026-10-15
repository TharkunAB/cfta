import MicroCFTA.InternedFreshOrdinaryProbeHeap
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Filtered probes through the actual optional intersection binder

The source binder compiles its stored body with actual available captures.
Repaired construction retains both filtered probes even at pending outcomes.
The unused branch has no constructor effect.
-/
namespace MicroCFTA.SourceRecursiveIntersectionProbeEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution (leaves encode leaves_available)
open InternedFreshOrdinaryProbeHeap (Heap)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual optional binders preserve filtered Mu probes at every source outcome. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (heap : Heap state)
    (available : Available state body) :
    Heap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
  have context := SourceRecursiveIntersectionSemanticHeap.context state semantic (leaves body) (leaves_available body state available)
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body state state semantic.1.normal.facts available]
  split
  · exact InternedFreshOrdinaryProbeHeap.build_heap _ _ state context heap
  · simpa only [InternedNestedConstruction.Outcome.state] using heap

end MicroCFTA.SourceRecursiveIntersectionProbeEffects
