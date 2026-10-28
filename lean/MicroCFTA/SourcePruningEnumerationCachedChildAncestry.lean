import MicroCFTA.SourcePruningEnumerationCachedChild

namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual child allocation retains old keys and gives the fresh slot the expansion keys. -/
theorem allocate_ancestry
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {node : Option Nat} {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    {fresh : Nat}
    (aligned : before.core.counter = before.core.values.length)
    (observed : allocate heap node before = some (fresh, after)) :
    fresh = before.core.counter ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.expansionAncestry = before.core.expansionAncestry ∧
      after.core.values[fresh]? = some (.unenumerated node []) ∧
      (∀ slot, slot < before.core.counter → ∀ key,
        key ∈ before.core.recursionAncestry slot → key ∈ after.core.recursionAncestry slot) ∧
      (∀ key, key ∈ before.core.expansionAncestry → key ∈ after.core.recursionAncestry fresh) := by
  unfold allocate at observed
  rcases Option.map_eq_some_iff.mp observed with ⟨flag, _classified, same⟩
  have freshSame : fresh = before.core.counter := (congrArg Prod.fst same).symm
  have coreSame : after.core = EnumerationState.allocated node before.core :=
    (congrArg (fun result : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard =>
      result.2.core) same).symm
  refine ⟨freshSame, ?_, ?_, ?_, ?_, ?_⟩
  · rw [coreSame]
    rfl
  · rw [coreSame]
    rfl
  · rw [freshSame, coreSame]
    exact EnumerationState.allocated_slot node before.core aligned
  · intro slot inside key member
    have different : slot ≠ before.core.counter := Nat.ne_of_lt inside
    simpa only [coreSame, EnumerationState.allocated, ite_eq_right different] using member
  · intro key member
    rw [freshSame, coreSame]
    simp only [EnumerationState.allocated, ↓reduceIte, List.mem_eraseDups, List.mem_append]
    exact Or.inl member

end MicroCFTA.SourcePruningEnumerationCachedChild
