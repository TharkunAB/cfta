/-- An actual finalizer changes only the captured slot and expansion ancestry. -/
private theorem finalized_core
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} := by
  unfold SourcePruningEnumerationFinalize.run at observed
  dsimp only [EnumerationExpandableIndex.frame] at observed
  cases stored : before.core.values[target]? with
  | none =>
      simp only [stored, Option.bind_none] at observed
      cases observed
  | some old =>
      simp only [stored, Option.bind_some] at observed
      unfold SourcePruningEnumerationNativeIndex.write at observed
      simp only [SourcePruningEnumerationNativeIndex.candidate, Option.bind_some] at observed
      cases counted : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives (-1)
          (references old) before.waiting with
      | none =>
          simp only [counted, Option.bind_none] at observed
          cases observed
      | some waiting =>
          simp only [counted, Option.bind_some, SourcePruningEnumerationNativeIndex.count,
            Option.some.injEq] at observed
          subst after
          rfl
