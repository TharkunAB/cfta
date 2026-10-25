import MicroCFTA.SourcePruningEnumerationObservation
import MicroCFTA.SourcePruningEnumerationReread
import MicroCFTA.MergedOrdinaryHeight

namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance entryMonadList : Monad List := {
  pure := fun value => [value]
  bind := fun values continuation => values.flatMap continuation
}

/-- Read a pending handle, capture its root, and set expansion ancestry. -/
def enter (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv : Nat) : EnumerateM Symbol EnumGuard
      (Nat × Nat × List EnumerationState.Suspended ×
        InternedConstructorTemplates.Value Symbol NativeGuard) := do
  match ← getValue fuel uv with
  | .unenumerated (some handle) scs =>
      let target ← representative fuel uv
      match lookupNode heap handle with
      | none => failure .unresolvedReference
      | some decoded =>
          modify fun state => {state with expansionAncestry :=
            if MergedOrdinaryHeight.recursiveBoundary decoded then
              (recursionKey handle scs :: state.recursionAncestry target).eraseDups
            else state.recursionAncestry target}
          pure (target, handle, scs, decoded)
  | _ => reject

/-- Derive stable entry execution and its retained storage and realized slots. -/
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
    {before with representatives := firstFound.forest}
  have readExact : ∀ (extra : Nat), ExceptT.run (getValue (readFuel + extra) uv before) =
    [.ok (readValue, readAfter)] := by
    intro extra
    change (getValue (readFuel + extra) uv before : List _) = _
    unfold getValue
    rw [bind_single _ _ before readAfter firstFound.representative
      (representative_exact _ uv before firstFound
        (UnionFind.findRoot_moreFuel readFuel extra before.representatives uv firstFound firstRun))]
    dsimp [rawValue, readAfter, get, getThe, MonadStateOf.get, bind, pure, StateT.bind,
      StateT.pure, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk]
    rw [stored]
    rfl
  have readSuccess : Success (getValue readFuel uv) before readValue readAfter := by
    simp only [Success, readExact 0, List.mem_singleton]
  have readFrame : Frame before readAfter := by
    exact (getValue_frame readFuel uv before readAfter readValue storage.total readSuccess).1
  have readStorage : StorageValid readAfter := by
    exact representative_storage before storage readFuel uv inside firstFound firstRun
  cases readValue with
  | enumerated fragment =>
      refine ⟨readFuel, _, readAfter, readExact, readFrame, ?_⟩
      intro extra
      change enter heap (readFuel + extra) uv before = []
      unfold enter
      rw [bind_single _ _ before readAfter _ (readExact extra)]
      rfl
  | eliminated =>
      refine ⟨readFuel, _, readAfter, readExact, readFrame, ?_⟩
      intro extra
      change enter heap (readFuel + extra) uv before = []
      unfold enter
      rw [bind_single _ _ before readAfter _ (readExact extra)]
      rfl
  | unenumerated node scs =>
    cases node with
    | none =>
      refine ⟨readFuel, _, readAfter, readExact, readFrame, ?_⟩
      intro extra
      change enter heap (readFuel + extra) uv before = []
      unfold enter
      rw [bind_single _ _ before readAfter _ (readExact extra)]
      rfl
    | some handle =>
      obtain ⟨target, _size, captureFuel, compressed, _firstFrame, _originalPath,
          captureSuccess, _rereadFrame, fullFrame, storedCapture, _rootBound⟩ :=
        SourcePruningEnumerationReread.pending_reread_complete readFuel uv handle scs
          before readAfter readAfter storage.total readSuccess (Frame.refl readAfter)
      obtain ⟨captured, captureRun, targetEq, compressedEq⟩ :=
        (EnumerationSchedule.representative_success captureFuel uv readAfter compressed target).mp
          captureSuccess
      have captureExact : ∀ (extra : Nat),
        ExceptT.run (representative (readFuel + captureFuel + extra) uv readAfter) =
          [.ok (target, compressed)] := by
        intro extra
        rw [targetEq, compressedEq]
        exact representative_exact _ uv readAfter captured (by
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            UnionFind.findRoot_moreFuel captureFuel (readFuel + extra)
              readAfter.representatives uv captured captureRun)
      have compressedStorage : StorageValid compressed := by
        rw [compressedEq]
        exact representative_storage readAfter readStorage captureFuel uv inside captured captureRun
      obtain ⟨decoded, decodedLookup, available, closed⟩ := realized target handle scs (by
        simpa only [fullFrame.values] using storedCapture)
      let entered : EnumerationState.State Symbol EnumGuard :=
        {compressed with expansionAncestry :=
          if MergedOrdinaryHeight.recursiveBoundary decoded then
            (recursionKey handle scs :: compressed.recursionAncestry target).eraseDups
          else compressed.recursionAncestry target}
      have enteredStorage : StorageValid entered := by
        exact ⟨compressedStorage.aligned, compressedStorage.total, compressedStorage.forest,
          compressedStorage.values, compressedStorage.guards⟩
      have enteredRealized : PendingRealized heap entered := by
        intro slot node scs stored
        apply realized slot node scs
        simpa only [entered, fullFrame.values] using stored
      refine ⟨readFuel + captureFuel, _, readAfter, ?_, readFrame,
        target, decoded, compressed, entered, fullFrame, ?_, storedCapture,
        decodedLookup, available, closed, rfl, ?_, enteredStorage, enteredRealized⟩
      · intro extra
        simpa only [Nat.add_assoc] using readExact (captureFuel + extra)
      · intro extra
        exact captureExact extra
      · intro extra
        change enter heap (readFuel + captureFuel + extra) uv before = _
        unfold enter
        rw [bind_single _ _ before readAfter _ (by
          simpa only [Nat.add_assoc] using readExact (captureFuel + extra))]
        dsimp only
        rw [bind_single _ _ readAfter compressed target (captureExact extra)]
        simp only [decodedLookup]
        rfl

end MicroCFTA.SourcePruningEnumerationEntry
