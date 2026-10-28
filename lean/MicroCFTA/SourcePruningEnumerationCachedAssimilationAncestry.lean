import MicroCFTA.SourcePruningEnumerationCachedAssimilation

namespace MicroCFTA.SourcePruningEnumerationCachedAssimilation
open EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

private theorem native_write_ancestry
    {heap : InternedConstructorTemplates.State Symbol Constraint}
    {fuel target : Nat} {value : UVarValue Symbol}
    {gained lost : List Suspended} {before after : Cached}
    (observed : SourcePruningEnumerationNativeIndex.write heap fuel target value
      gained lost before = some after) :
    after.core.recursionAncestry = before.core.recursionAncestry := by
  unfold SourcePruningEnumerationNativeIndex.write at observed
  rcases Option.bind_eq_some_iff.mp observed with ⟨flag, _classified, observed⟩
  rcases Option.bind_eq_some_iff.mp observed with ⟨removed, _removed, observed⟩
  rcases Option.bind_eq_some_iff.mp observed with ⟨saved, _saved, observed⟩
  cases observed
  rfl

/-- Actual assimilation retains each slot's keys and transfers source keys to the target. -/
theorem finish_ancestry
    {heap : InternedConstructorTemplates.State Symbol Constraint}
    {fuel source target : Nat} {merged : Option Nat}
    {sourceScs targetScs : List Suspended} {before after : Cached}
    {rows : List (Unit × Cached)}
    (observed : finish heap fuel source target merged sourceScs targetScs before =
      some (rows, after)) :
    (∀ slot key, key ∈ before.core.recursionAncestry slot →
      key ∈ after.core.recursionAncestry slot) ∧
    (merged ≠ some 0 → ∀ key, key ∈ before.core.recursionAncestry source →
      key ∈ after.core.recursionAncestry target) := by
  by_cases rejected : merged = some 0
  · rw [finish, ite_eq_left rejected] at observed
    have afterSame : before = after := congrArg Prod.snd (Option.some.inj observed)
    rw [← afterSame]
    exact ⟨fun _ _ member => member, fun nonempty => False.elim (nonempty rejected)⟩
  · unfold finish at observed
    rw [ite_eq_right rejected] at observed
    rcases Option.bind_eq_some_iff.mp observed with ⟨targetAfter, targetWritten, observed⟩
    rcases Option.map_eq_some_iff.mp observed with ⟨sourceAfter, sourceWritten, rowsSame⟩
    have first := native_write_ancestry targetWritten
    have second := native_write_ancestry sourceWritten
    let finished : Cached := EnumerationExpandableIndex.frame
      {sourceAfter.core with recursionAncestry := fun other =>
        if other = target then
          (sourceAfter.core.recursionAncestry source ++
            sourceAfter.core.recursionAncestry target).eraseDups
        else sourceAfter.core.recursionAncestry other} sourceAfter
    have endpoint : finished = after := congrArg Prod.snd rowsSame
    have ancestry : after.core.recursionAncestry = fun other =>
        if other = target then
          (before.core.recursionAncestry source ++
            before.core.recursionAncestry target).eraseDups
        else before.core.recursionAncestry other := by
      rw [← endpoint]
      change (fun other => if other = target then
        (sourceAfter.core.recursionAncestry source ++
          sourceAfter.core.recursionAncestry target).eraseDups
        else sourceAfter.core.recursionAncestry other) = _
      rw [second, first]
    constructor
    · intro slot key member
      rw [ancestry]
      by_cases same : slot = target
      · subst slot
        simp only [↓reduceIte, List.mem_eraseDups, List.mem_append]
        exact Or.inr member
      · simpa only [ite_eq_right same] using member
    · intro _ key member
      rw [ancestry]
      simp only [↓reduceIte, List.mem_eraseDups, List.mem_append]
      exact Or.inl member

end MicroCFTA.SourcePruningEnumerationCachedAssimilation
