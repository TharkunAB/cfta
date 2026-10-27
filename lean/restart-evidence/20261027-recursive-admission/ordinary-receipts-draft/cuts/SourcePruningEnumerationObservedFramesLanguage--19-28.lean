theorem enter_semantics
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : InternedConstructorTemplates.Value Symbol NativeGuard)
    (total : UnionFind.Total before.representatives)
    (observed : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    ∀ (language : NodeLanguage Symbol) (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      Satisfies language residualMeaning assignment after ↔
        Satisfies language residualMeaning assignment before := by
