  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Check the actual native boundary and clear the bucket only for a repeated recursion key. -/
def checkRepeated (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended) : EnumerateM Symbol EnumGuard Bool := do
  match lookupNode heap handle with
  | none => failure .unresolvedReference
  | some value =>
      if MergedOrdinaryHeight.recursiveBoundary value then
        let root ← representative fuel uv
        let current : EnumerationState.State Symbol EnumGuard ← get
        if recursionKey handle scs ∈ current.recursionAncestry root then
          setValue root (.unenumerated (some handle) [])
          pure true
        else pure false
      else pure false

/-- The actual native recursion guard derives finite execution and both indexed cache outcomes. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (uv handle : Nat) (scs : List Suspended) (value : Value Symbol NativeGuard) (roots : Nat → Nat)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (realized : PendingRealized heap before.core)
    (decoded : lookupNode heap handle = some value)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (fuel : Nat) (repeated : Bool) (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      (∀ extra, ExceptT.run (checkRepeated heap (fuel + extra) uv handle scs before.core) =
        [.ok (repeated, after.core)]) ∧
      EnumerationDriver.Ready uv after.core ∧ Roots after.core.representatives roots ∧
      PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ held, EnumerationReferences.IncomingAvoid held before.core → EnumerationReferences.IncomingAvoid held after.core) ∧
      (repeated = false → Frame before.core after.core ∧ after.expandable = before.expandable ∧
        after.waiting = before.waiting ∧ after.core.values[uv]? = some (.unenumerated (some handle) scs)) ∧
      (repeated = true → MergedOrdinaryHeight.recursiveBoundary value = true ∧
        after.core.values[uv]? = some (.unenumerated (some handle) []) ∧ after.expandable uv = false ∧
        after.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
        ∃ (resolved : EnumerationState.State Symbol EnumGuard) (countFuel : Nat),
          Frame before.core resolved ∧
          Success (representative fuel uv) before.core uv resolved ∧
          recursionKey handle scs ∈ resolved.recursionAncestry uv ∧
          Success (setValue uv (.unenumerated (some handle) [])) resolved () after.core ∧
          ∀ extra, SourcePruningEnumerationNativeIndex.write heap (countFuel + extra) uv
            (.unenumerated (some handle) []) [] scs (EnumerationExpandableIndex.frame resolved before) = some after) := by
  by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
