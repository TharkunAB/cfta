theorem IsolatedPending.through_finalize
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target held handle : Nat) (fragment : Fragments.Fragment Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (isolated : IsolatedPending held handle before.core) (different : target ≠ held)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    IsolatedPending held handle after.core := by
  have core := finalized_core heap fuel target fragment before after observed
  refine ⟨?_, ?_, ?_⟩
  · simpa only [core] using isolated.root
  · simpa only [core, List.getElem?_set_ne different] using isolated.stored
  · intro value member sc listed same
    rw [core] at member same
    rcases List.mem_or_eq_of_mem_set member with old | replaced
    · exact isolated.incoming value old sc listed same
    · subst value
      simp [references] at listed

section Resources
open SourcePruningEnumerationRecursive (Packet)
