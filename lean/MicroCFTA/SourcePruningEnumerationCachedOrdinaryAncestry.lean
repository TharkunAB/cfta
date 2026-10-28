import MicroCFTA.SourcePruningEnumerationCachedChildAncestry

namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

private theorem writeSlot_core
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel target : Nat} {value : UVarValue Symbol}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    (observed : writeSlot heap fuel target value before = some after) :
    after.core = {before.core with values := before.core.values.set target value} := by
  unfold writeSlot at observed
  rcases Option.bind_eq_some_iff.mp observed with ⟨old, _stored, observed⟩
  unfold SourcePruningEnumerationNativeIndex.write at observed
  rcases Option.bind_eq_some_iff.mp observed with ⟨flag, _classified, observed⟩
  rcases Option.bind_eq_some_iff.mp observed with ⟨removed, _removed, observed⟩
  rcases Option.bind_eq_some_iff.mp observed with ⟨saved, _saved, observed⟩
  cases observed
  rfl

/-- The actual ordinary bucket write retains old keys and the fresh slot's expansion keys. -/
theorem prepareOrdinary_ancestry
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel : Nat} {scs : List Suspended}
    {value : InternedConstructorTemplates.Value Symbol NativeGuard}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    {fragment : Fragments.Fragment Symbol}
    (aligned : before.core.counter = before.core.values.length)
    (observed : prepareOrdinary heap fuel scs value before = some (fragment, after)) :
    fragment = .hole before.core.counter ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.expansionAncestry = before.core.expansionAncestry ∧
      (∃ handle, encodeNode value = some handle ∧
        after.core.values[before.core.counter]? = some (.unenumerated (some handle) scs)) ∧
      (∀ slot, slot < before.core.counter → ∀ key,
        key ∈ before.core.recursionAncestry slot → key ∈ after.core.recursionAncestry slot) ∧
      (∀ key, key ∈ before.core.expansionAncestry →
        key ∈ after.core.recursionAncestry before.core.counter) := by
  cases value with
  | empty | reference | union | mu => simp [prepareOrdinary] at observed
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareOrdinary, terminal] at observed
      · simp only [prepareOrdinary, ite_eq_right terminal] at observed
        rcases Option.bind_eq_some_iff.mp observed with ⟨handle, encoded, observed⟩
        rcases Option.bind_eq_some_iff.mp observed with ⟨allocation, allocated, observed⟩
        rcases allocation with ⟨fresh, middle⟩
        rcases Option.map_eq_some_iff.mp observed with ⟨returned, written, same⟩
        rcases Prod.mk.inj same with ⟨rfl, rfl⟩
        obtain ⟨freshName, allocationCounter, allocationExpansion, allocatedStored, oldKeys, freshKeys⟩ :=
          allocate_ancestry aligned allocated
        have writtenCore := writeSlot_core written
        refine ⟨?_, ?_, ?_, ⟨handle, encoded, ?_⟩, ?_, ?_⟩
        · rw [freshName]
        · simpa only [writtenCore] using allocationCounter
        · simpa only [writtenCore] using allocationExpansion
        · rw [writtenCore, ← freshName]
          exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp allocatedStored).1
        · intro slot inside key member
          rw [writtenCore]
          exact oldKeys slot inside key member
        · intro key member
          rw [writtenCore, ← freshName]
          exact freshKeys key member

end MicroCFTA.SourcePruningEnumerationCachedChild
