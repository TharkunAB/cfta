import MicroCFTA.SourcePruningEnumerationKeyAncestry

/-!
# Finite historical key shapes through actual cached writes

Native writes change values and indexes without adding keys.
Ordinary child preparation inherits the same fixed key-shape carrier.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeIndex
open EnumerationState SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual native bucket write preserves both historical key fields. -/
theorem write_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel target : Nat} {value : UVarValue Symbol} {gained lost : List Suspended}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    (bounded : KeyAncestry carrier before.core)
    (observed : write heap fuel target value gained lost before = some after) :
    KeyAncestry carrier after.core := by
  unfold write at observed
  obtain ⟨_flag, _classified, observed⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨_removed, _removedCounts, observed⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨_saved, _savedCounts, observed⟩ := Option.bind_eq_some_iff.mp observed
  cases observed
  exact bounded

end MicroCFTA.SourcePruningEnumerationNativeIndex

namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- The actual old-slot read and write retain the original key-shape carrier. -/
theorem writeSlot_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel target : Nat} {value : UVarValue Symbol}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    (bounded : KeyAncestry carrier before.core)
    (observed : writeSlot heap fuel target value before = some after) :
    KeyAncestry carrier after.core := by
  unfold writeSlot at observed
  obtain ⟨_old, _stored, written⟩ := Option.bind_eq_some_iff.mp observed
  exact SourcePruningEnumerationNativeIndex.write_key_ancestry bounded written

/-- Actual ordinary child allocation and its bucket write preserve historical key shapes. -/
theorem prepareOrdinary_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel : Nat} {scs : List Suspended}
    {value : InternedConstructorTemplates.Value Symbol NativeGuard}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    {fragment : Fragments.Fragment Symbol}
    (bounded : KeyAncestry carrier before.core)
    (observed : prepareOrdinary heap fuel scs value before = some (fragment, after)) :
    KeyAncestry carrier after.core := by
  cases value with
  | empty | reference | union | mu => simp [prepareOrdinary] at observed
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareOrdinary, terminal] at observed
      · simp only [prepareOrdinary, ite_eq_right terminal] at observed
        obtain ⟨_handle, _encoded, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨allocation, allocated, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨_fresh, _middle⟩ := allocation
        obtain ⟨returned, written, same⟩ := Option.map_eq_some_iff.mp observed
        have finalBounded := writeSlot_key_ancestry (allocate_key_ancestry bounded allocated) written
        have cacheSame : returned = after := congrArg Prod.snd same
        simpa only [cacheSame] using finalBounded

end MicroCFTA.SourcePruningEnumerationCachedChild
