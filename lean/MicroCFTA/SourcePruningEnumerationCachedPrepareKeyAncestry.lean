import MicroCFTA.SourcePruningEnumerationKeyAncestryStorage
import MicroCFTA.SourcePruningEnumerationCachedPrepare

/-!
# Historical key shapes through actual shallow child preparation

Ordinary writes and opaque allocations retain the original carrier.
Empty rejection returns the original cache.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open EnumerationState SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every row of an actual supported preparation retains the original carrier. -/
theorem rows_key_ancestry
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    {carrier : List (List (List (List Nat)))}
    (bounded : KeyAncestry carrier before.core)
    (observed : prepareChild heap fuel scs value before = some rows) :
    ∀ fragment after, (fragment, after) ∈ rows → KeyAncestry carrier after.core := by
  cases value with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at observed
      subst rows
      intro fragment after member
      cases member
  | reference => simp [prepareChild] at observed
  | node entry edges depth free =>
      simp only [prepareChild, Option.map_eq_some_iff] at observed
      obtain ⟨result, prepared, rowsSame⟩ := observed
      subst rows
      intro fragment after member
      have same : after = result.2 := congrArg Prod.snd (List.mem_singleton.mp member)
      rw [same]
      exact SourcePruningEnumerationCachedChild.prepareOrdinary_key_ancestry bounded prepared
  | union entry members depth free | mu entry members depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareChild, terminal] at observed
      · simp only [prepareChild, ite_eq_right terminal] at observed
        obtain ⟨_handle, _encoded, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨allocation, allocated, rowsSame⟩ := Option.map_eq_some_iff.mp observed
        subst rows
        intro fragment after member
        have same : after = allocation.2 := congrArg Prod.snd (List.mem_singleton.mp member)
        rw [same]
        exact SourcePruningEnumerationCachedChild.allocate_key_ancestry bounded allocated

/-- Every actual shallow cache candidate retains the carrier, including rejection. -/
theorem cache_key_ancestry
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    {carrier : List (List (List (List Nat)))}
    (bounded : KeyAncestry carrier before.core)
    (observed : (match prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) : KeyAncestry carrier after.core := by
  cases prepared : prepareChild heap fuel scs value before with
  | none => simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact bounded
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              exact rows_key_ancestry heap fuel scs value before [(fragment, reached)]
                bounded prepared fragment reached (by simp)
          | cons row rest => simp only [prepared, reduceCtorEq] at observed

end MicroCFTA.SourcePruningEnumerationCachedPrepare
