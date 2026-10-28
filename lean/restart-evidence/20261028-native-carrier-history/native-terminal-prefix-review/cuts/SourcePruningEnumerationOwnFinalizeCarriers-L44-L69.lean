    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    (references : ReferencesCarry before.core)
    (observed : suspendMany heap tries before = some (suspended, after)) :
    PreservesCarriers before.core after.core ∧ ReferencesCarry after.core := by
  induction tries generalizing before after suspended with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have cacheSame : before = after := congrArg Prod.snd same
      subst after
      exact ⟨.refl before.core, references⟩
  | cons trie rest ih =>
      simp only [suspendMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocated, result, continued, same⟩ := observed
      obtain ⟨allocatedCarriers, allocatedReferences⟩ :=
        SourcePruningEnumerationCachedChild.allocate_carriers heap none before allocation.2
          allocation.1 references allocated
      obtain ⟨resultCarriers, resultReferences⟩ := ih allocation.2 result.2 result.1
        allocatedReferences continued
      have cacheSame : result.2 = after := congrArg Prod.snd same
      rw [← cacheSame]
      exact ⟨allocatedCarriers.trans resultCarriers, resultReferences⟩

end MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState EnumerationCorrectness EnumerationSchedule
