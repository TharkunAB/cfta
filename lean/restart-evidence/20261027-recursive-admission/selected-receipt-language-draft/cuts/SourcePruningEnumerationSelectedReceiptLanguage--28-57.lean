private theorem entry_values
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv : Nat)
    (before after : Core) (target handle : Nat) (bucket : List Suspended) (decoded : Node)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningEnumerationEntry.enter heap fuel uv)
      before (target, handle, bucket, decoded) after) : after.values = before.values := by
  unfold SourcePruningEnumerationEntry.enter at observed
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
  have readFrame := (getValue_frame fuel uv before read value total reading).1
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have fullFrame := readFrame.trans
            (representative_frame fuel uv found read compressed (readFrame.total total) compressing)
          cases lookup : lookupNode heap storedHandle with
          | none =>
              simp only [lookup] at continued
              exact (success_failure .unresolvedReference compressed after _ continued).elim
          | some actual =>
              simp only [lookup] at continued
              obtain ⟨ignored, entered, modifying, final⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
              obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
              exact fullFrame.values
