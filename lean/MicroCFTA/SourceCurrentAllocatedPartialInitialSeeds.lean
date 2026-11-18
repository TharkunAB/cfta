import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentNativeNumericalSeedInvariant

namespace MicroCFTA.SourceCurrentAllocatedPartialInitialization
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
set_option autoImplicit false

/- Note [Cold initial source seeds]
The literal initializer retains the supplied source heap.
Both native memo tables start empty.
NoNewMu is reflexive and every Returned obligation uses returned_empty.
No stored Mu or body identity premise is needed for this initial fact.
This lemma does not assert that any Mu record exists in the source heap.
-/

theorem checked_initial_source_seeds
    (width : Nat) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : InternedConstructorTemplates.Value Symbol Guard)
    (bodyId : Nat) :
    SourceCurrentNativeNumericalSeedInvariant.Seeds sourceHeap entry body depth ordinary bodyId
      (checked width cache sourceHeap) := by
  dsimp only [SourceCurrentNativeNumericalSeedInvariant.Seeds, checked,
    SourceRecursiveIntersectionThunks.initial]
  refine ⟨InternedShallowHeap.noNewMu_refl sourceHeap,
    SourceCurrentAllocatedNativeContextCache.returned_empty _,
    SourceCurrentAllocatedNativeContextCache.returned_empty _,
    SourceCurrentAllocatedNativeContextCache.returned_empty _,
    SourceCurrentAllocatedNativeContextCache.returned_empty _, ?_⟩
  intro patternId _ _
  exact ⟨SourceCurrentAllocatedNativeContextCache.returned_empty _,
    SourceCurrentAllocatedNativeContextCache.returned_empty _,
    SourceCurrentAllocatedNativeContextCache.returned_empty _,
    SourceCurrentAllocatedNativeContextCache.returned_empty _⟩

end MicroCFTA.SourceCurrentAllocatedPartialInitialization
