import MicroCFTA.SourcePruningEnumerationClear
import MicroCFTA.SourcePruningEnumerationEntry
import MicroCFTA.SourcePruningEnumerationSelection

namespace MicroCFTA.SourcePruningEnumerationRecursion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance recursionMonadList : Monad List where
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
  · obtain ⟨fuel, root, resolved, read, _total⟩ :=
      EnumerationExecution.representative_terminates before.core ready.safe.1.total uv
    obtain ⟨same, resolvedSafe, counter, rootFrame⟩ := EnumerationDriver.representative_root fuel uv root
      before.core resolved ready.safe ready.inside ready.root read
    subst root
    have frame := representative_frame fuel uv uv before.core resolved ready.safe.1.total read
    obtain ⟨found, lookup, representativeSame, resolvedSame⟩ :=
      (representative_success fuel uv before.core resolved uv).mp read
    have readExact : ∀ extra, ExceptT.run (representative (fuel + extra) uv before.core) =
        [.ok (uv, resolved)] := by
      intro extra
      change representative (fuel + extra) uv before.core = [.ok (uv, resolved)]
      simpa only [← representativeSame, ← resolvedSame] using representative_exact _ uv before.core found
        (UnionFind.findRoot_moreFuel fuel extra before.core.representatives uv found lookup)
    have resolvedReady : EnumerationDriver.Ready uv resolved := by
      refine ⟨resolvedSafe, by simpa only [counter] using ready.inside, rootFrame.root, ?_⟩
      intro node bucket read
      exact rootFrame.avoids bucket (ready.avoids node bucket (by simpa only [frame.values] using read))
    have resolvedPaths : Roots resolved.representatives roots := by
      intro slot
      obtain ⟨size, path⟩ := paths slot
      exact ⟨size, (frame.reaches slot (roots slot) size).mpr path⟩
    have resolvedStored : resolved.values[uv]? = some (.unenumerated (some handle) scs) := by
      simpa only [frame.values] using stored
    have resolvedRealized : PendingRealized heap resolved := by
      intro slot node bucket read
      exact realized slot node bucket (by simpa only [frame.values] using read)
    have resolvedCounts : EnumerationCanonicalWaiting.Correct roots resolved.values before.waiting := by
      simpa only [frame.values] using counts
    have resolvedFlags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((resolved.values[slot]?).getD .eliminated) = some (before.expandable slot) := by
      simpa only [frame.values] using flags
    by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
    · let written : EnumerationState.State Symbol EnumGuard :=
        {resolved with values := resolved.values.set uv (.unenumerated (some handle) [])}
      have writing : Success (setValue uv (.unenumerated (some handle) [])) resolved () written :=
        (EnumerationDriver.modify_success _ resolved written).mpr rfl
      obtain ⟨countFuel, after, counted, core, waiting, _expandable, parked, afterReady, afterPaths,
        afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming⟩ :=
        SourcePruningEnumerationClear.complete heap (EnumerationExpandableIndex.frame resolved before) written
          uv handle scs value roots resolvedReady resolvedStored resolvedRealized decoded boundary resolvedPaths
          resolvedCounts resolvedFlags writing
      refine ⟨fuel, true, after, ?_, core ▸ afterReady, core ▸ afterPaths, core ▸ afterRealized,
        core ▸ afterCounts, core ▸ afterFlags, ?_, ?_, (by intro impossible; cases impossible), ?_⟩
      · intro extra
        change checkRepeated heap (fuel + extra) uv handle scs before.core = _
        unfold checkRepeated
        rw [decoded]
        simp only [boundary, ↓reduceIte]
        rw [bind_single _ _ before.core resolved uv (readExact extra)]
        simp [get, getThe, MonadStateOf.get, setValue, modify, modifyGet, MonadStateOf.modifyGet,
          bind, pure, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
          ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, seen, ← core, written]
      · intro history
        exact core ▸ afterPending (EnumerationPendingReplacement.frame_pending before.core resolved frame history)
      · intro held incoming
        exact core ▸ afterIncoming held (EnumerationPendingReplacement.frame_incoming held before.core resolved frame incoming)
      · intro _
        exact ⟨boundary, core ▸ afterStored, parked, waiting,
          resolved, countFuel, frame, read, seen, core ▸ writing, counted⟩
    · let after := EnumerationExpandableIndex.frame resolved before
      refine ⟨fuel, false, after, ?_, resolvedReady, resolvedPaths, resolvedRealized, resolvedCounts,
        resolvedFlags, EnumerationPendingReplacement.frame_pending before.core resolved frame,
        fun held => EnumerationPendingReplacement.frame_incoming held before.core resolved frame,
        (fun _ => ⟨frame, rfl, rfl, resolvedStored⟩), (by intro impossible; cases impossible)⟩
      intro extra
      change checkRepeated heap (fuel + extra) uv handle scs before.core = _
      unfold checkRepeated
      rw [decoded]
      simp only [boundary, ↓reduceIte]
      rw [bind_single _ _ before.core resolved uv (readExact extra)]
      simp [get, getThe, MonadStateOf.get, bind, pure, StateT.bind, StateT.pure, StateT.get,
        ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, seen, after, EnumerationExpandableIndex.frame]
  · refine ⟨0, false, before, ?_, ready, paths, realized, counts, flags, (fun history => history),
      (fun _ incoming => incoming), (fun _ => ⟨.refl _, rfl, rfl, stored⟩),
      (by intro impossible; cases impossible)⟩
    intro extra
    simp [checkRepeated, decoded, boundary, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

/-- Original pure selection derives the actual value read and native recursion check. -/
theorem selected_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (safe : Safe before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (readFuel handle : Nat) (scs : List Suspended) (value : Value Symbol NativeGuard)
      (readAfter : EnumerationState.State Symbol EnumGuard) (checkFuel : Nat) (repeated : Bool)
      (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      lookupNode heap handle = some value ∧ Available heap value ∧ value.free = [] ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)]) ∧
      Frame before.core readAfter ∧
      (∀ extra, ExceptT.run (checkRepeated heap (checkFuel + extra) uv handle scs readAfter) =
        [.ok (repeated, after.core)]) ∧
      EnumerationDriver.Ready uv after.core ∧ Roots after.core.representatives roots ∧
      PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumerationReferences.IncomingAvoid uv after.core ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (repeated = false → Frame before.core after.core ∧ after.expandable = before.expandable ∧
        after.waiting = before.waiting ∧ after.core.values[uv]? = some (.unenumerated (some handle) scs)) ∧
      (repeated = true → MergedOrdinaryHeight.recursiveBoundary value = true ∧
        after.core.values[uv]? = some (.unenumerated (some handle) []) ∧ after.expandable uv = false ∧
        after.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
        ∃ (resolved : EnumerationState.State Symbol EnumGuard) (countFuel : Nat),
          Frame before.core resolved ∧
          Success (representative checkFuel uv) readAfter uv resolved ∧
          recursionKey handle scs ∈ resolved.recursionAncestry uv ∧
          Success (setValue uv (.unenumerated (some handle) [])) resolved () after.core ∧
          ∀ extra, SourcePruningEnumerationNativeIndex.write heap (countFuel + extra) uv
            (.unenumerated (some handle) []) [] scs (EnumerationExpandableIndex.frame resolved before) = some after) := by
  have ready := SourcePruningEnumerationSelection.ready heap before preference uv safe roots paths counts flags selection
  have incoming := SourcePruningEnumerationSelection.incoming heap before preference uv safe roots paths counts flags selection
  obtain ⟨handle, scs, value, stored, decoded, available, closed, _candidate⟩ :=
    SourcePruningEnumerationSelection.realized heap before preference uv safe.1.aligned realized flags selection
  obtain ⟨readFuel, readValue, readAfter, readExact, readFrame, _entry⟩ :=
    SourcePruningEnumerationEntry.complete heap before.core uv safe.1 ready.inside realized
  have read : Success (getValue readFuel uv) before.core readValue readAfter := by
    rw [Success, ← Nat.add_zero readFuel, readExact 0]
    exact List.mem_singleton_self _
  obtain ⟨_readSafe, _readCounter, rootFrame, readStored⟩ := EnumerationDriver.getValue_root
    readFuel uv before.core readAfter readValue safe ready.inside ready.root read
  have same : readValue = .unenumerated (some handle) scs :=
    Option.some.inj (readStored.symm.trans (rootFrame.value.trans stored))
  subst readValue
  have readReady := EnumerationDriver.getValue_ready readFuel uv before.core readAfter
    (.unenumerated (some handle) scs) ready read
  have readPaths : Roots readAfter.representatives roots := by
    intro slot
    obtain ⟨size, path⟩ := paths slot
    exact ⟨size, (readFrame.reaches slot (roots slot) size).mpr path⟩
  have readRealized : PendingRealized heap readAfter := by
    intro slot node bucket stored
    exact realized slot node bucket (by simpa only [readFrame.values] using stored)
  obtain ⟨checkFuel, repeated, after, checked, afterReady, afterPaths, afterRealized, afterCounts,
    afterFlags, afterPending, afterIncoming, continued, parked⟩ :=
    complete heap (EnumerationExpandableIndex.frame readAfter before) uv handle scs value roots
      readReady.1 readStored readRealized decoded readPaths
      (by simpa only [EnumerationExpandableIndex.frame, readFrame.values] using counts)
      (by simpa only [EnumerationExpandableIndex.frame, readFrame.values] using flags)
  refine ⟨readFuel, handle, scs, value, readAfter, checkFuel, repeated, after, stored, decoded, available, closed,
    readExact, readFrame, checked, afterReady, afterPaths, afterRealized, afterCounts, afterFlags,
    afterIncoming uv (EnumerationPendingReplacement.frame_incoming uv before.core readAfter readFrame incoming),
    (fun history => afterPending (EnumerationPendingReplacement.frame_pending before.core readAfter readFrame history)),
    ?_, ?_⟩
  · intro notRepeated
    obtain ⟨checkFrame, sameFlags, sameWaiting, stored⟩ := continued notRepeated
    exact ⟨readFrame.trans checkFrame, sameFlags, sameWaiting, stored⟩
  · intro repeated
    obtain ⟨boundary, cleared, disabled, waiting, resolved, countFuel, checkFrame, readRoot, seen, written, indexed⟩ := parked repeated
    exact ⟨boundary, cleared, disabled, waiting, resolved, countFuel,
      readFrame.trans checkFrame, readRoot, seen, written, indexed⟩

end MicroCFTA.SourcePruningEnumerationRecursion
