      expansionAncestry := []}) :
    PreservesCarriers before after ∧ ReferencesCarry after ∧ FragmentCarries after fragment := by
  subst after
  have actual := write_references before target fragment references holes
  exact ⟨actual.1, actual.2, holes.preserve fragment actual.1⟩

/-- An actual indexed finalization retains graph carriers at its exact returned cache. -/
theorem run_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (references : ReferencesCarry before.core) (holes : FragmentCarries before.core fragment)
    (observed : run heap fuel target fragment before = some after) :
    PreservesCarriers before.core after.core ∧ ReferencesCarry after.core ∧
      FragmentCarries after.core fragment := by
  simp only [run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  exact written_carriers before.core _ target fragment references holes rfl

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCarriers EnumerationGraphReferences
