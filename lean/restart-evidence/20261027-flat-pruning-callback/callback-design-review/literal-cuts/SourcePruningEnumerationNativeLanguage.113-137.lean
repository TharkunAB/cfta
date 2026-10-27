theorem satisfies_frame (language : NodeLanguage Symbol)
    (residualMeaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (before after : EnumerationState.State Symbol EnumGuard) (frame : Frame before after) :
    Satisfies language residualMeaning assignment after ↔ Satisfies language residualMeaning assignment before := by
  have forestSame : UnionFind.Satisfies after.representatives assignment ↔
      UnionFind.Satisfies before.representatives assignment := by
    constructor
    · intro satisfied left right related
      exact satisfied left right ((frame_sameClass before after frame left right).mpr related)
    · intro satisfied left right related
      exact satisfied left right ((frame_sameClass before after frame left right).mp related)
  simp only [Satisfies, Fragments.stateSatisfies, frame.values, frame.obligations, forestSame]

/-- Actual native growth and an enumeration frame retain the same complete assignments. -/
theorem satisfies_keeps_frame
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (beforeHeap afterHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (residualMeaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (realized : PendingRealized beforeHeap before) (frame : Frame before after)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap) :
    Satisfies (handles holds ambient afterHeap) residualMeaning assignment after ↔
      Satisfies (handles holds ambient beforeHeap) residualMeaning assignment before :=
  (satisfies_frame (handles holds ambient afterHeap) residualMeaning assignment before after frame).trans
    (satisfies_keeps holds ambient beforeHeap afterHeap before residualMeaning assignment realized kept)
