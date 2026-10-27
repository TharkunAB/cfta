theorem allocated_avoids_bounded
    (before : EnumerationState.State Symbol EnumGuard) (handle : Nat) (safe : Safe before)
    (bucket : List Suspended) (bounded : ∀ sc ∈ bucket, sc.var < before.counter) :
    Avoids (allocated (some handle) before).representatives before.counter bucket := by
  intro sc member same
  change UnionFind.SameClass before.representatives before.counter sc.var at same
  have equal := outside_class before.representatives before.counter before.counter sc.var
    safe.1.forest (Nat.le_refl _) same
