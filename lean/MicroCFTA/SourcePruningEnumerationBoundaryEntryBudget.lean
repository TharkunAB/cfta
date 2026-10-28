import MicroCFTA.SourcePruningEnumerationCheckedBoundaryBudget

/-!
# Strict shape consumption at the actual native boundary entry

Entry preserves every per-slot history and sets the active expansion history.
Its actual representative agrees with the preceding false boundary check.
The original model supplies the finite carrier for the exact inserted key.
The returned expansion history has a strictly smaller unused shape budget.
-/
namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- An actual Entry result exposes its resolved path and exact history update. -/
theorem enter_history
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : InternedConstructorTemplates.Value Symbol NativeGuard)
    (total : UnionFind.Total before.representatives)
    (observed : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    ∃ size, UnionFind.Reaches before.representatives uv target size ∧
      lookupNode heap handle = some decoded ∧
      after.recursionAncestry = before.recursionAncestry ∧
      after.expansionAncestry =
        if MergedOrdinaryHeight.recursiveBoundary decoded then
          (recursionKey handle bucket :: before.recursionAncestry target).eraseDups
        else before.recursionAncestry target := by
  unfold enter at observed
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
          obtain ⟨resolved, resolving, rootSame, compressedSame⟩ :=
            (representative_success fuel uv read compressed found).mp compressing
          cases lookup : lookupNode heap storedHandle with
          | none =>
              simp only [lookup] at continued
              exact (success_failure .unresolvedReference compressed after _ continued).elim
          | some actual =>
              simp only [lookup] at continued
              obtain ⟨ignored, entered, modifying, final⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
              obtain ⟨same, afterSame⟩ := (success_pure _ _ _ _).mp final
              obtain ⟨targetSame, tailSame⟩ := Prod.mk.inj same
              obtain ⟨handleSame, tailSame⟩ := Prod.mk.inj tailSame
              obtain ⟨bucketSame, decodedSame⟩ := Prod.mk.inj tailSame
              refine ⟨resolved.size, ?_, ?_, ?_, ?_⟩
              · rw [targetSame, rootSame]
                exact (readFrame.reaches uv resolved.representative resolved.size).mp
                  (UnionFind.findRoot_correct fuel read.representatives uv resolved resolving).1
              · rw [handleSame, decodedSame]
                exact lookup
              · rw [afterSame]
                change compressed.recursionAncestry = before.recursionAncestry
                rw [compressedSame]
                exact readFrame.recursionAncestry
              · rw [afterSame, targetSame, handleSame, bucketSame, decodedSame]
                change (if MergedOrdinaryHeight.recursiveBoundary actual then
                  (recursionKey storedHandle scs :: compressed.recursionAncestry found).eraseDups
                  else compressed.recursionAncestry found) = _
                rw [compressedSame, readFrame.recursionAncestry]

end MicroCFTA.SourcePruningEnumerationEntry

namespace MicroCFTA.SourcePruningEnumerationBoundaryEntryBudget
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open SourcePruningEnumerationNodes SourcePruningEnumerationOrigins
open SourcePruningEnumerationModelKeyShapes SourcePruningEnumerationKeyShapeBudget
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- The original model and actual false check force strict consumption at the actual Entry result. -/
theorem checked_enter_shape_budget
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (checkFuel entryFuel uv target handle : Nat) (bucket : List Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before checked entering after : EnumerationState.State Symbol EnumGuard)
    (total : UnionFind.Total before.representatives)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv handle bucket)
      before false checked)
    (intervening : Frame checked entering)
    (entered : ExceptT.run (SourcePruningEnumerationEntry.enter heap entryFuel uv entering) =
      [.ok ((target, handle, bucket, value), after)])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before)
    (origins : AssignmentOrigins whole before.counter assignment)
    (canonical : EnumerationValidity.Canonical before) (inside : uv < before.counter)
    (stored : before.values[uv]? = some (.unenumerated (some handle) bucket)) :
    lookupNode heap handle = some value ∧
      Success (representative checkFuel uv) before target checked ∧
      after.recursionAncestry = before.recursionAncestry ∧
      after.expansionAncestry =
        (recursionKey handle bucket :: checked.recursionAncestry target).eraseDups ∧
      (recursionKey handle bucket).tries ∈
        unused (keyShapes whole) handle (checked.recursionAncestry target) ∧
      (unused (keyShapes whole) handle after.expansionAncestry).length <
        (unused (keyShapes whole) handle (checked.recursionAncestry target)).length := by
  have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
    heap checkFuel uv handle bucket before checked total checking
  have fullFrame := checkFrame.trans intervening
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter heap entryFuel uv)
      entering (target, handle, bucket, value) after := by
    rw [Success, entered]
    exact List.mem_singleton_self _
  obtain ⟨size, targetPath, decoded, histories, expansion⟩ :=
    SourcePruningEnumerationEntry.enter_history heap entryFuel uv entering after target handle bucket value
      (fullFrame.total total) entrySuccess
  obtain ⟨root, resolving, fresh⟩ := SourcePruningEnumerationRecursionOrder.checkRepeated_false_fresh
    heap checkFuel uv handle bucket value before checked decoded boundary checking
  obtain ⟨found, foundRun, rootSame, _checkedSame⟩ :=
    (representative_success checkFuel uv before checked root).mp resolving
  have rootPath : UnionFind.Reaches before.representatives uv root found.size := by
    rw [rootSame]
    exact (UnionFind.findRoot_correct checkFuel before.representatives uv found foundRun).1
  have same : root = target :=
    (UnionFind.reaches_unique rootPath ((fullFrame.reaches uv target size).mp targetPath)).1
  rw [same] at resolving fresh
  have member := stored_recursion_key_mem language meaning before whole assignment
    satisfied origins canonical inside stored
  have expansionSame : after.expansionAncestry =
      (recursionKey handle bucket :: checked.recursionAncestry target).eraseDups := by
    simpa only [boundary, ↓reduceIte, intervening.recursionAncestry] using expansion
  refine ⟨decoded, resolving, histories.trans fullFrame.recursionAncestry, expansionSame, ?_, ?_⟩
  · simp only [unused, List.mem_filter, decide_eq_true_eq]
    exact ⟨member, fresh⟩
  · rw [expansionSame]
    exact unused_insert_lt (keyShapes whole) (recursionKey handle bucket)
      (checked.recursionAncestry target) member fresh

end MicroCFTA.SourcePruningEnumerationBoundaryEntryBudget
