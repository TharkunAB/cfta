import MicroCFTA.SourcePruningEnumerationIdentity
import MicroCFTA.SourcePruningEnumerationWrites
import MicroCFTA.SourcePruningEnumerationReread

namespace MicroCFTA.SourcePruningEnumerationNarrowing
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation SourcePruningNativeView
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Key : Type}

local instance narrowingMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Compute narrowing and retain the actual enumeration branch effects. -/
theorem narrow_pending_complete
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol NativeGuard)]
    (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol NativeGuard → Bool) (key : Key)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before readAfter entry : EnumerationState.State Symbol EnumGuard)
    (readFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (ready : SourceEqualityRequiredCache.Ready heap) (realized : PendingRealized heap before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (entered : Frame readAfter entry) :
    ∃ (oldValue result : InternedConstructorTemplates.Value Symbol NativeGuard) (nativeFuel : Nat)
      (nextHeap : InternedConstructorTemplates.State Symbol NativeGuard) (newHandle : Nat),
      lookupNode heap oldHandle = some oldValue ∧ encodeNode oldValue = some oldHandle ∧
      Available heap oldValue ∧ oldValue.free = [] ∧
      narrowAt fits admits nativeFuel key oldValue heap = .done result nextHeap ∧
      (∀ extra, narrowAt fits admits (nativeFuel + extra) key oldValue heap = .done result nextHeap) ∧
      SourceEqualityRequiredCache.Keeps heap nextHeap ∧ Available nextHeap result ∧ result.free = [] ∧
      encodeNode result = some newHandle ∧ lookupNode nextHeap newHandle = some result ∧
      lookupNode nextHeap oldHandle = some oldValue ∧
      Frame before readAfter ∧ PendingRealized nextHeap entry ∧
      (result ≠ .empty → oldValue ≠ .empty) ∧
      (result = .empty → ¬ ∃ final : EnumerationState.State Symbol EnumGuard,
        Success (reject : EnumerateM Symbol EnumGuard Unit) entry () final) ∧
      (result ≠ .empty → newHandle = oldHandle →
        result = oldValue ∧ Success (pure () : EnumerateM Symbol EnumGuard Unit) entry () entry) ∧
      (result ≠ .empty → newHandle ≠ oldHandle →
        ∃ (root size rereadFuel : Nat) (rereadAfter final : EnumerationState.State Symbol EnumGuard),
          UnionFind.Reaches before.representatives uv root size ∧
          Success (representative rereadFuel uv) entry root rereadAfter ∧
          Frame entry rereadAfter ∧ Frame before rereadAfter ∧
          rereadAfter.values[root]? = some (.unenumerated (some oldHandle) scs) ∧
          root < rereadAfter.values.length ∧ PendingRealized nextHeap rereadAfter ∧
          Success (setValue root (.unenumerated (some newHandle) scs)) rereadAfter () final ∧
          final = {rereadAfter with values := rereadAfter.values.set root (.unenumerated (some newHandle) scs)} ∧
          final.values[root]? = some (.unenumerated (some newHandle) scs) ∧ PendingRealized nextHeap final ∧
          Success (representative rereadFuel uv >>= fun selected =>
            setValue selected (.unenumerated (some newHandle) scs)) entry () final) := by
  obtain ⟨found, _lookup, stored, _readState⟩ :=
    (getValue_success readFuel uv before readAfter (.unenumerated (some oldHandle) scs)).mp observed
  obtain ⟨oldValue, oldDecoded, oldAvailable, oldClosed⟩ :=
    realized found.representative oldHandle scs stored
  have oldEncoded : encodeNode oldValue = some oldHandle := by
    exact SourcePruningEnumerationIdentity.lookup_encode heap oldHandle oldValue
      ready.semantic.1.normal.facts.coherent oldDecoded
  have firstFrame : Frame before readAfter := by
    exact (getValue_frame readFuel uv before readAfter (.unenumerated (some oldHandle) scs) total observed).1
  obtain ⟨nativeFuel, _rows, _middle, result, nextHeap, _exposed, _built, narrowed, kept,
      resultAvailable, resultClosed, _ordinary, _resultRows, _secondRead, _emptyIff, _rowsEmptyIff, stable⟩ :=
    narrowAt_complete fits admits key oldValue heap ready oldAvailable oldClosed
  obtain ⟨newHandle, newEncoded, newDecoded⟩ :=
    available_readback nextHeap result kept.ready.semantic.1.normal.facts.coherent resultAvailable resultClosed
  have oldRetained : lookupNode nextHeap oldHandle = some oldValue := by
    exact lookupNode_keeps heap nextHeap kept oldHandle oldValue oldDecoded
  have entryRealized : PendingRealized nextHeap entry := by
    exact realized_preserved heap nextHeap before entry realized (firstFrame.trans entered) kept
  have survivingOld : result ≠ .empty → oldValue ≠ .empty := by
    intro survives wasEmpty
    rw [wasEmpty, SourcePruningEnumerationIdentity.narrowAt_empty] at narrowed
    exact survives (MergedSourceComparison.Result.done.inj narrowed).1.symm
  refine ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, oldEncoded,
    oldAvailable, oldClosed, narrowed, stable, kept, resultAvailable, resultClosed,
    newEncoded, newDecoded, oldRetained, firstFrame, entryRealized, survivingOld, ?_, ?_, ?_⟩
  · intro _emptyResult
    simp [Success, reject, ExceptT.run]
  · intro _nonempty sameHandle
    exact ⟨Option.some.inj ((sameHandle ▸ newDecoded).symm.trans oldRetained),
      (success_pure () () entry entry).mpr ⟨rfl, rfl⟩⟩
  · intro _nonempty _changed
    obtain ⟨root, size, rereadFuel, rereadAfter, _repeatedFirstFrame, path,
        reread, entryFrame, beforeFrame, oldSlot, inside⟩ :=
      SourcePruningEnumerationReread.pending_reread_complete readFuel uv oldHandle scs
        before readAfter entry total observed entered
    have rereadRealized : PendingRealized nextHeap rereadAfter := by
      exact realized_preserved heap nextHeap before rereadAfter realized beforeFrame kept
    obtain ⟨writtenHandle, final, writtenEncoded, write, exactFinal, newSlot, finalRealized⟩ :=
      SourcePruningEnumerationWrites.write_available_realized nextHeap rereadAfter result root scs
        kept.ready.semantic.1.normal.facts.coherent resultAvailable resultClosed rereadRealized inside
    have writtenSame : writtenHandle = newHandle := by
      exact Option.some.inj (writtenEncoded.symm.trans newEncoded)
    subst writtenHandle
    refine ⟨root, size, rereadFuel, rereadAfter, final, path, reread, entryFrame, beforeFrame,
      oldSlot, inside, rereadRealized, write, exactFinal, newSlot, finalRealized, ?_⟩
    exact (success_bind (representative rereadFuel uv)
      (fun selected => setValue selected (.unenumerated (some newHandle) scs)) entry () final).mpr
      ⟨root, rereadAfter, reread, write⟩

end MicroCFTA.SourcePruningEnumerationNarrowing
