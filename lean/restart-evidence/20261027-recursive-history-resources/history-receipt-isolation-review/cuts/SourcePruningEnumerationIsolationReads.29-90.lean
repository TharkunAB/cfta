/-- An actual pending entry retains isolation through compression and its ancestry write. -/
theorem IsolatedPending.through_enter
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (held heldHandle target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (isolated : IsolatedPending held heldHandle before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningEnumerationEntry.enter heap fuel uv) before
      (target, handle, bucket, decoded) after) : IsolatedPending held heldHandle after := by
  unfold SourcePruningEnumerationEntry.enter at observed
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
  have readFrame := (getValue_frame fuel uv before read value total reading).1
  have readIsolated := isolated.through_frame readFrame
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have frame := representative_frame fuel uv found read compressed (readFrame.total total) compressing
          have compressedIsolated := readIsolated.through_frame frame
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
              exact ⟨compressedIsolated.root, compressedIsolated.stored, compressedIsolated.incoming⟩

/-- The literal ordinary-entry row certifies isolation at that row's own core. -/
theorem IsolatedPending.through_entry_row
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (held heldHandle target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (isolated : IsolatedPending held heldHandle before)
    (total : UnionFind.Total before.representatives)
    (observed : ExceptT.run (SourcePruningEnumerationEntry.enter heap fuel uv before) =
      [.ok ((target, handle, bucket, decoded), after)]) : IsolatedPending held heldHandle after := by
  apply isolated.through_enter heap fuel uv before after held heldHandle target handle bucket decoded total
  rw [Success, observed]
  exact List.mem_singleton_self _

/-- Either successful recording side and either Boolean result retain the same isolated core slot. -/
theorem IsolatedPending.through_recordTypes {Typing : Type}
    (graph : Graph Symbol EnumGuard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat)
    (before after : EnumerationState.State Symbol EnumGuard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (isolated : IsolatedPending held handle before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) : IsolatedPending held handle after :=
  isolated.through_frame
    (SourcePruningRecordTypes.recordTypes_frame graph templates fuel metadata uv input
      before after result total observed)
