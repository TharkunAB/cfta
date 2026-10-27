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
