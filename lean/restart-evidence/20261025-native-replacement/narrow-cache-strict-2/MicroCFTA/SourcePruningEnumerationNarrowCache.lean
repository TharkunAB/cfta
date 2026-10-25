import MicroCFTA.SourcePruningEnumerationAction
import MicroCFTA.SourcePruningEnumerationReplacement

namespace MicroCFTA.SourcePruningEnumerationNarrowCache
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing Key : Type}

local instance narrowCacheMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Actual narrowing derives the same native result and its complete indexed enumeration cache. -/
theorem complete
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol NativeGuard → Bool)
    (metadata : Metadata Typing) (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (readAfter : EnumerationState.State Symbol EnumGuard)
    (readFuel uv oldHandle : Nat) (scs : List Suspended) (roots : Nat → Nat)
    (nativeReady : SourceEqualityRequiredCache.Ready heap)
    (ready : EnumerationDriver.Ready uv before.core)
    (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (read : Success (getValue readFuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter) :
    ∃ (oldValue result : InternedConstructorTemplates.Value Symbol NativeGuard) (nativeFuel : Nat)
      (nextHeap : InternedConstructorTemplates.State Symbol NativeGuard) (newHandle : Nat),
      lookupNode heap oldHandle = some oldValue ∧
      SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap = .done result nextHeap ∧
      (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue heap =
        .done result nextHeap) ∧
      SourceEqualityRequiredCache.Keeps heap nextHeap ∧ Available nextHeap result ∧ result.free = [] ∧
      encodeNode result = some newHandle ∧ lookupNode nextHeap newHandle = some result ∧
      (result = .empty → ∀ representativeFuel,
        SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv
          oldHandle scs oldValue heap = .done (result, some (reject : EnumerateM Symbol EnumGuard Unit)) nextHeap ∧
        ¬ ∃ final : EnumerationState.State Symbol EnumGuard,
          Success (reject : EnumerateM Symbol EnumGuard Unit) readAfter () final) ∧
      (result ≠ .empty →
        ∃ (representativeFuel countFuel : Nat) (action : EnumerateM Symbol EnumGuard Unit)
          (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
          SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv
            oldHandle scs oldValue heap = .done (result, some action) nextHeap ∧
          Success action readAfter () after.core ∧
          ((newHandle = oldHandle ∧ after = EnumerationExpandableIndex.frame readAfter before) ∨
            (newHandle ≠ oldHandle ∧ ∃ rereadAfter : EnumerationState.State Symbol EnumGuard,
              Success (representative representativeFuel uv) readAfter uv rereadAfter ∧
              Success (setValue uv (.unenumerated (some newHandle) scs)) rereadAfter () after.core ∧
              ∀ extra, SourcePruningEnumerationNativeIndex.write nextHeap (countFuel + extra) uv
                (.unenumerated (some newHandle) scs) scs scs
                (EnumerationExpandableIndex.frame rereadAfter before) = some after)) ∧
          after.waiting = before.waiting ∧ EnumerationDriver.Ready uv after.core ∧
          Roots after.core.representatives roots ∧ PendingRealized nextHeap after.core ∧
          after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
          EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
          (∀ slot, SourcePruningEnumerationNativeIndex.candidate nextHeap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
          (∀ held, EnumerationReferences.IncomingAvoid held before.core →
            EnumerationReferences.IncomingAvoid held after.core)) := by
  obtain ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, _oldEncoded,
    _oldAvailable, _oldClosed, narrowed, stable, kept, resultAvailable, resultClosed,
    newEncoded, newDecoded, _oldRetained, firstFrame, entryRealized, entryPending, entryIncoming,
    _survivingOld, emptyBranch, equalBranch, changedBranch⟩ :=
    SourcePruningEnumerationAction.prepare_pending_complete holeKey fits admits metadata heap
      before.core readAfter readAfter readFuel uv oldHandle scs nativeReady realized ready.safe.1.total read (.refl _)
  refine ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, narrowed, stable, kept,
    resultAvailable, resultClosed, newEncoded, newDecoded, emptyBranch, ?_⟩
  intro nonempty
  by_cases sameHandle : newHandle = oldHandle
  · obtain ⟨_sameValue, prepared, observed⟩ := equalBranch nonempty sameHandle
    let after := EnumerationExpandableIndex.frame readAfter before
    have afterReady := (EnumerationDriver.getValue_ready readFuel uv before.core readAfter _ ready read).1
    have afterStored := (EnumerationDriver.getValue_root readFuel uv before.core readAfter _
      ready.safe ready.inside ready.root read).2.2.2
    have afterPaths : Roots after.core.representatives roots := by
      intro slot
      obtain ⟨size, path⟩ := paths slot
      exact ⟨size, (firstFrame.reaches slot (roots slot) size).mpr path⟩
    have grownFlags := SourcePruningEnumerationNativeGrowth.flags heap nextHeap kept before flags
    refine ⟨0, 0, pure (), after, prepared 0, observed, .inl ⟨sameHandle, rfl⟩,
      rfl, afterReady, afterPaths, entryRealized, ?_, ?_, ?_, entryPending, entryIncoming⟩
    · simpa only [after, EnumerationExpandableIndex.frame, sameHandle] using afterStored
    · simpa only [after, EnumerationExpandableIndex.frame, firstFrame.values] using counts
    · simpa only [after, EnumerationExpandableIndex.frame, firstFrame.values] using grownFlags
  · obtain ⟨root, _size, rereadFuel, rereadAfter, final, _rootPath, reread, _secondFrame,
      _wholeFrame, _oldStored, _bound, _rereadRealized, written, _finalShape, _finalStored,
      _finalRealized, _pendingHistory, _incomingHistory, prepared, observed⟩ := changedBranch nonempty sameHandle
    obtain ⟨sameRoot, _wholeFrame, countFuel, cached, cachedRun, core, waiting, _expandable,
      afterReady, afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming⟩ :=
      SourcePruningEnumerationReplacement.after_read heap nextHeap kept before readAfter rereadAfter final
        readFuel rereadFuel uv root oldHandle newHandle scs result roots ready paths realized
        newDecoded resultAvailable resultClosed counts flags read reread written
    subst root
    subst final
    exact ⟨rereadFuel, countFuel, representative rereadFuel uv >>= fun selected =>
      setValue selected (.unenumerated (some newHandle) scs), cached, prepared, observed,
      .inr ⟨sameHandle, rereadAfter, reread, written, cachedRun⟩, waiting, afterReady, afterPaths, afterRealized,
      afterStored, afterCounts, afterFlags, afterPending, afterIncoming⟩

end MicroCFTA.SourcePruningEnumerationNarrowCache
