private theorem finalized_core
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} := by
