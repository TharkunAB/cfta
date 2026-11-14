import MicroCFTA.SourcePruningEnumerationBoundaryEntryBudget

/-!
# Full stored buckets at actual native entries

Status: UNCOMPILED CANDIDATE.
The supplied successful execution fixes its own fuel and input state.
The result retains the original target, full bucket, and history update.
This module does not derive a complete branch history or a finite assignment.
-/
namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- Actual entry reads its full bucket at its returned root in the original state. -/
theorem enter_recorded_bucket_origin
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : InternedConstructorTemplates.Value Symbol NativeGuard)
    (total : UnionFind.Total before.representatives)
    (observed : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    ∃ size, UnionFind.Reaches before.representatives uv target size ∧
      before.values[target]? = some (.unenumerated (some handle) bucket) ∧
      after.values = before.values ∧
      lookupNode heap handle = some decoded ∧
      after.recursionAncestry = before.recursionAncestry ∧
      after.expansionAncestry =
        if MergedOrdinaryHeight.recursiveBoundary decoded then
          (recursionKey handle bucket :: before.recursionAncestry target).eraseDups
        else before.recursionAncestry target := by
  obtain ⟨size, path, decodedLookup, histories, expansion⟩ :=
    enter_history heap fuel uv before after target handle bucket decoded total observed
  have fields :
      before.values[target]? = some (.unenumerated (some handle) bucket) ∧
      after.values = before.values := by
    unfold enter at observed
    obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
    obtain ⟨readFrame, readRoot, _readSize, readPath, _readAfterPath, stored⟩ :=
      getValue_frame fuel uv before read value total reading
    have storedAtTarget : before.values[target]? = some value := by
      have sameRoot : readRoot = target := (UnionFind.reaches_unique readPath path).1
      simpa only [sameRoot] using stored
    cases value with
    | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
    | eliminated => exact (reject_unsuccessful read after _ continued).elim
    | unenumerated node scs =>
        cases node with
        | none => exact (reject_unsuccessful read after _ continued).elim
        | some storedHandle =>
            obtain ⟨found, compressed, compressing, continued⟩ :=
              (success_bind _ _ _ _ _).mp continued
            have compressedFrame := representative_frame fuel uv found read compressed
              (readFrame.total total) compressing
            cases lookup : lookupNode heap storedHandle with
            | none =>
                simp only [lookup] at continued
                exact (success_failure .unresolvedReference compressed after _ continued).elim
            | some actual =>
                simp only [lookup] at continued
                obtain ⟨ignored, entered, modifying, final⟩ :=
                  (success_bind _ _ _ _ _).mp continued
                cases ignored
                obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
                obtain ⟨same, afterSame⟩ := (success_pure _ _ _ _).mp final
                obtain ⟨_targetSame, tailSame⟩ := Prod.mk.inj same
                obtain ⟨handleSame, tailSame⟩ := Prod.mk.inj tailSame
                obtain ⟨bucketSame, _decodedSame⟩ := Prod.mk.inj tailSame
                constructor
                · rw [handleSame, bucketSame]
                  exact storedAtTarget
                · rw [afterSame]
                  change compressed.values = before.values
                  exact compressedFrame.values.trans readFrame.values
  exact ⟨size, path, fields.1, fields.2, decodedLookup, histories, expansion⟩

/-- Each active key comes from the old target history or this actual full entry. -/
theorem enter_active_key_origin
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : InternedConstructorTemplates.Value Symbol NativeGuard)
    (total : UnionFind.Total before.representatives)
    (observed : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after)
    (key : RecursionKey) (member : key ∈ after.expansionAncestry) :
    key ∈ before.recursionAncestry target ∨
      (MergedOrdinaryHeight.recursiveBoundary decoded = true ∧
        key = recursionKey handle bucket) := by
  obtain ⟨_size, _path, _decodedLookup, _histories, expansion⟩ :=
    enter_history heap fuel uv before after target handle bucket decoded total observed
  by_cases boundary : MergedOrdinaryHeight.recursiveBoundary decoded = true
  · have alternatives : key = recursionKey handle bucket ∨
        key ∈ before.recursionAncestry target := by
      simpa only [expansion, boundary, ↓reduceIte, List.mem_eraseDups, List.mem_cons] using member
    rcases alternatives with inserted | previous
    · exact .inr ⟨boundary, inserted⟩
    · exact .inl previous
  · exact .inl (by simpa only [expansion, boundary, ↓reduceIte] using member)

end MicroCFTA.SourcePruningEnumerationEntry

#check @MicroCFTA.SourcePruningEnumerationEntryRecordedBucketOrigin.observed_entry_bucket_origin
#print axioms MicroCFTA.SourcePruningEnumerationEntryRecordedBucketOrigin.observed_entry_bucket_origin
#check @MicroCFTA.SourcePruningEnumerationEntryRecordedBucketOrigin.observed_entry_active_history_key_origin
#print axioms MicroCFTA.SourcePruningEnumerationEntryRecordedBucketOrigin.observed_entry_active_history_key_origin
