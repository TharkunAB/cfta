import MicroCFTA.SourcePruningEnumerationKeyAncestryStorage
import MicroCFTA.SourcePruningEnumerationCachedAssimilation

/-!
# Finite historical key shapes through actual cached assimilation

An empty merge retains the original cache.
Both actual native writes preserve the fixed carrier.
The final ancestry union contains only keys from the two retained lists.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedAssimilation
open EnumerationState SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- Actual rejected or completed cached assimilation preserves the original key-shape carrier. -/
theorem finish_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {heap : InternedConstructorTemplates.State Symbol Constraint}
    {fuel source target : Nat} {merged : Option Nat}
    {sourceScs targetScs : List Suspended} {before after : Cached}
    {rows : List (Unit × Cached)}
    (bounded : KeyAncestry carrier before.core)
    (observed : finish heap fuel source target merged sourceScs targetScs before =
      some (rows, after)) : KeyAncestry carrier after.core := by
  by_cases rejected : merged = some 0
  · rw [finish, ite_eq_left rejected] at observed
    have cacheSame : before = after := congrArg Prod.snd (Option.some.inj observed)
    simpa only [cacheSame] using bounded
  · unfold finish at observed
    rw [ite_eq_right rejected] at observed
    obtain ⟨targetAfter, targetWritten, observed⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨sourceAfter, sourceWritten, same⟩ := Option.map_eq_some_iff.mp observed
    have first := SourcePruningEnumerationNativeIndex.write_key_ancestry bounded targetWritten
    have second := SourcePruningEnumerationNativeIndex.write_key_ancestry first sourceWritten
    let finished : Cached := EnumerationExpandableIndex.frame
      {sourceAfter.core with recursionAncestry := fun other =>
        if other = target then
          (sourceAfter.core.recursionAncestry source ++ sourceAfter.core.recursionAncestry target).eraseDups
        else sourceAfter.core.recursionAncestry other} sourceAfter
    have endpoint : finished = after := congrArg Prod.snd same
    rw [← endpoint]
    refine ⟨?_, second.2⟩
    intro slot key member
    change key ∈ (if slot = target then
      (sourceAfter.core.recursionAncestry source ++ sourceAfter.core.recursionAncestry target).eraseDups
      else sourceAfter.core.recursionAncestry slot) at member
    by_cases current : slot = target
    · simp only [ite_eq_left current, List.mem_eraseDups, List.mem_append] at member
      exact member.elim (second.1 source key) (second.1 target key)
    · exact second.1 slot key (by simpa only [ite_eq_right current] using member)

end MicroCFTA.SourcePruningEnumerationCachedAssimilation
