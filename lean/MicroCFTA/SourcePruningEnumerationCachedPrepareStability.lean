import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.SourcePruningEnumerationNativeIndexStability

/-!
# Stable successful child cache preparation

A successful index pass retains the complete prepared cache at larger bounds.
Failed index passes are outside the statement.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState EnumerationSchedule SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- A successful full-constraint slot write is stable at larger index bounds. -/
theorem writeSlot_some_stable
    {heap : InternedConstructorTemplates.State Symbol NativeGuard} {k K target : Nat}
    {value : UVarValue Symbol} {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    (observed : writeSlot heap k target value before = some after) (enough : k ≤ K) :
    writeSlot heap K target value before = some after := by
  simp only [writeSlot, Option.bind_eq_some_iff] at observed
  obtain ⟨old, stored, written⟩ := observed
  simp only [writeSlot, stored, Option.bind_some]
  have later := SourcePruningEnumerationNativeIndex.write_some_moreFuel heap k (K - k)
    target value (references value) (references old) before after written
  have sameFuel : k + (K - k) = K := by omega
  simpa only [sameFuel] using later

/-- A successful ordinary preparation retains its exact fragment and cache. -/
theorem prepareOrdinary_some_stable
    {heap : InternedConstructorTemplates.State Symbol NativeGuard} {k K : Nat}
    {scs : List Suspended} {value : InternedConstructorTemplates.Value Symbol NativeGuard}
    {before : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    {result : Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard}
    (observed : prepareOrdinary heap k scs value before = some result) (enough : k ≤ K) :
    prepareOrdinary heap K scs value before = some result := by
  cases value with
  | empty => simpa only [prepareOrdinary] using observed
  | reference name => simpa only [prepareOrdinary] using observed
  | union entry members depth free => simpa only [prepareOrdinary] using observed
  | mu entry body depthShape ordinaryShape => simpa only [prepareOrdinary] using observed
  | node entry edges depth free =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp only [prepareOrdinary, terminal, ↓reduceIte] at observed
      cases observed
    · simp only [prepareOrdinary, terminal, Bool.false_eq_true, ↓reduceIte,
        Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨handle, encoded, allocation, allocated, after, written, same⟩ := observed
      have later := writeSlot_some_stable written enough
      simpa only [prepareOrdinary, terminal, Bool.false_eq_true, ↓reduceIte, encoded,
        Option.bind_some, allocated, later, Option.map_some, Option.some.injEq] using same

end MicroCFTA.SourcePruningEnumerationCachedChild

namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open EnumerationState
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every successful cached child preparation retains its whole row list. -/
theorem prepareChild_some_stable
    {heap : InternedConstructorTemplates.State Symbol NativeGuard} {k K : Nat}
    {scs : List Suspended} {value : InternedConstructorTemplates.Value Symbol NativeGuard}
    {before : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    {rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard)}
    (observed : prepareChild heap k scs value before = some rows) (enough : k ≤ K) :
    prepareChild heap K scs value before = some rows := by
  cases value with
  | empty => simpa only [prepareChild] using observed
  | reference name => simpa only [prepareChild] using observed
  | union entry members depth free => simpa only [prepareChild] using observed
  | mu entry body depthShape ordinaryShape => simpa only [prepareChild] using observed
  | node entry edges depth free =>
    simp only [prepareChild, Option.map_eq_some_iff] at observed
    obtain ⟨result, prepared, rfl⟩ := observed
    have later := SourcePruningEnumerationCachedChild.prepareOrdinary_some_stable prepared enough
    simp only [prepareChild, later, Option.map_some]

end MicroCFTA.SourcePruningEnumerationCachedPrepare
