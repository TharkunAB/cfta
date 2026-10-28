import MicroCFTA.SourcePruningEnumerationKeyShapeBudget
import MicroCFTA.SourcePruningEnumerationCachedChild

/-!
# Shape budgets inherited by actual child allocation

The fresh slot receives every current expansion key.
Old keys at the fresh counter can only reduce its unused shape count.
This result does not bound the native handle set.
-/
namespace MicroCFTA.SourcePruningEnumerationKeyShapeBudget
open EnumerationState
variable {Symbol Guard : Type}

/-- The allocated slot inherits the current expansion budget at every fixed handle. -/
theorem allocated_unused_le
    (carrier : List (List (List (List Nat)))) (handle : Nat)
    (before : State Symbol Guard) (node : Option Nat) :
    (unused carrier handle ((allocated node before).recursionAncestry before.counter)).length ≤
      (unused carrier handle before.expansionAncestry).length := by
  apply unused_mono
  intro key member
  change key ∈ (if before.counter = before.counter then
    (before.expansionAncestry ++ before.recursionAncestry before.counter).eraseDups
    else before.recursionAncestry before.counter)
  simp only [↓reduceIte, List.mem_eraseDups, List.mem_append]
  exact Or.inl member

end MicroCFTA.SourcePruningEnumerationKeyShapeBudget

namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState SourcePruningEnumerationKeyShapeBudget
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual cached allocation gives its returned child no more unused shapes. -/
theorem allocate_unused_le
    (carrier : List (List (List (List Nat)))) (handle : Nat)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (node : Option Nat)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (fresh : Nat)
    (observed : allocate heap node before = some (fresh, after)) :
    fresh = before.core.counter ∧
      (unused carrier handle (after.core.recursionAncestry fresh)).length ≤
        (unused carrier handle before.core.expansionAncestry).length := by
  unfold allocate at observed
  obtain ⟨_flag, _classified, same⟩ := Option.map_eq_some_iff.mp observed
  have freshSame : fresh = before.core.counter := (congrArg Prod.fst same).symm
  have coreSame : after.core = allocated node before.core :=
    (congrArg (fun result : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard => result.2.core) same).symm
  refine ⟨freshSame, ?_⟩
  rw [coreSame, freshSame]
  exact allocated_unused_le carrier handle before.core node

end MicroCFTA.SourcePruningEnumerationCachedChild
