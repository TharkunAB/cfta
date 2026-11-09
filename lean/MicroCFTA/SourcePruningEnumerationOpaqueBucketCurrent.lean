import MicroCFTA.SourcePruningEnumerationOpaqueBucketAssignment
import MicroCFTA.EnumerationCanonicalWaiting
import MicroCFTA.SourcePruningEnumerationNativeIndex

/-!
# Current cache facts for the two-slot assignment state

Both slots are unrestricted and have no native handle.
The cache has no waiting references and no candidate flags.
These facts do not require a native caller context or source history.
-/
namespace MicroCFTA.SourcePruningEnumerationOpaqueBucketCurrent
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- The literal two-slot state has empty waiting and candidate indexes. -/
def cache (EnumGuard : Type) : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
  ⟨SourcePruningEnumerationOpaqueBucketAssignment.before, fun _ => false, fun _ => none⟩

private theorem pure_value (value : UVarValue Symbol)
    (member : value ∈ (cache EnumGuard).core.values) :
    value = .unenumerated none [] := by
  simpa [cache, SourcePruningEnumerationOpaqueBucketAssignment.before] using member

/-- The actual initial cache satisfies every local state and native index prerequisite. -/
theorem current (native : InternedConstructorTemplates.State Symbol NativeGuard) :
    Safe (cache EnumGuard).core ∧
      EnumerationValidity.Canonical (cache EnumGuard).core ∧
      PendingRealized native (cache EnumGuard).core ∧
      Roots (cache EnumGuard).core.representatives id ∧
      EnumerationCanonicalWaiting.Correct id (cache EnumGuard).core.values (cache EnumGuard).waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate native
        (((cache EnumGuard).core.values[slot]?).getD .eliminated) =
          some ((cache EnumGuard).expandable slot)) ∧
      (∀ slot, EnumerationWaitingIndex.read (cache EnumGuard).waiting slot = 0) := by
  have storage : StorageValid (cache EnumGuard).core := by
    refine ⟨rfl, UnionFind.initial_total [0, 1], ?_, ?_, ?_⟩
    · change ForestBound 2 (UnionFind.withInitialValues [0, 1])
      intro uv entry found
      have member : uv ∈ [0, 1] := by
        by_cases present : uv ∈ [0, 1]
        · exact present
        · simp only [UnionFind.withInitialValues, ite_eq_right present] at found
          cases found
      have rootEntry : UnionFind.Entry.root 1 = entry :=
        Option.some.inj (by
          simpa only [UnionFind.withInitialValues, ite_eq_left member] using found)
      subst entry
      refine ⟨?_, trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide
    · intro value member
      obtain rfl := pure_value (EnumGuard := EnumGuard) value member
      simp [SlotBound]
    · simp [cache, SourcePruningEnumerationOpaqueBucketAssignment.before]
  have live : LiveRoots (cache EnumGuard).core := by
    intro uv value found
    obtain rfl := pure_value (EnumGuard := EnumGuard) value (List.mem_of_getElem? found)
    refine ⟨fun _ => ⟨1, .root (UnionFind.read_initial [0, 1] uv)⟩, ?_⟩
    intro _ impossible
    cases impossible
  refine ⟨⟨storage, live⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro value member
    obtain rfl := pure_value (EnumGuard := EnumGuard) value member
    simp [references, ValidSuspended]
  · intro slot node scs found
    have same := pure_value (EnumGuard := EnumGuard) (.unenumerated (some node) scs)
      (List.mem_of_getElem? found)
    cases same
  · intro uv
    exact ⟨1, .root (UnionFind.read_initial [0, 1] uv)⟩
  · intro uv
    rfl
  · intro slot
    cases slot with
    | zero => rfl
    | succ slot =>
        cases slot <;> rfl
  · intro slot
    rfl

end MicroCFTA.SourcePruningEnumerationOpaqueBucketCurrent
