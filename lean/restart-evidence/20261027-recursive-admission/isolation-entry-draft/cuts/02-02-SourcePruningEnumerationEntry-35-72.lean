theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard) (uv : Nat)
    (storage : StorageValid before) (inside : uv < before.counter)
    (realized : PendingRealized heap before) :
    ∃ (fuel : Nat) (readValue : EnumerationState.UVarValue Symbol)
      (readAfter : EnumerationState.State Symbol EnumGuard),
      (∀ (extra : Nat), ExceptT.run (getValue (fuel + extra) uv before) =
        [.ok (readValue, readAfter)]) ∧
      Frame before readAfter ∧
      match readValue with
      | .unenumerated (some handle) scs =>
          ∃ (target : Nat) (decoded : InternedConstructorTemplates.Value Symbol NativeGuard)
            (compressed entered : EnumerationState.State Symbol EnumGuard),
            Frame before compressed ∧
            (∀ (extra : Nat), ExceptT.run (representative (fuel + extra) uv readAfter) =
              [.ok (target, compressed)]) ∧
            compressed.values[target]? = some (.unenumerated (some handle) scs) ∧
            lookupNode heap handle = some decoded ∧
            InternedProbeProvenance.Available heap decoded ∧ decoded.free = [] ∧
            entered = {compressed with expansionAncestry :=
              if MergedOrdinaryHeight.recursiveBoundary decoded then
                (recursionKey handle scs :: compressed.recursionAncestry target).eraseDups
              else compressed.recursionAncestry target} ∧
            (∀ (extra : Nat), ExceptT.run (enter heap (fuel + extra) uv before) =
              [.ok ((target, handle, scs, decoded), entered)]) ∧
            StorageValid entered ∧ PendingRealized heap entered
      | _ => ∀ (extra : Nat), ExceptT.run (enter heap (fuel + extra) uv before) = [] := by
  obtain ⟨originalRoot, originalSize, path⟩ := storage.total uv
  obtain ⟨readFuel, firstFound, firstRun⟩ := UnionFind.findRoot_terminates path
  have firstInside : firstFound.representative < before.values.length := by
    rw [← storage.aligned]
    exact (findRoot_bounded readFuel before.representatives before.counter uv
      storage.forest inside firstFound firstRun).1
  obtain ⟨readValue, stored⟩ : ∃ value : EnumerationState.UVarValue Symbol,
      before.values[firstFound.representative]? = some value :=
    ⟨_, List.getElem?_eq_getElem firstInside⟩
  let readAfter : EnumerationState.State Symbol EnumGuard :=
