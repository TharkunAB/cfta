/-- Clear expansion ancestry and store the fragment at the captured raw slot. -/
def finish (target : Nat) (fragment : Fragments.Fragment Symbol) :
    EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol) := do
  modify fun state => {state with expansionAncestry := []}
  let _old ← rawValue target
  setValue target (.enumerated fragment)
  pure fragment

/-- Use the current raw value to remove its waiting references after reset. -/
def run (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  let reset : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
    EnumerationExpandableIndex.frame {before.core with expansionAncestry := []} before
  (reset.core.values[target]?).bind fun old =>
    SourcePruningEnumerationNativeIndex.write heap fuel target (.enumerated fragment)
      [] (references old) reset
