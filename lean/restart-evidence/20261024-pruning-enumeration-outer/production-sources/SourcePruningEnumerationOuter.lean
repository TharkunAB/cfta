import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.SourcePruningEnumerationNarrowing

namespace MicroCFTA.SourcePruningEnumerationOuter
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing Key : Type}

local instance outerMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Derive outer narrowing and retain the actual pending-slot branch effects. -/
theorem narrow_pending_complete
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol NativeGuard → Bool)
    (metadata : Metadata Typing) (heap : InternedConstructorTemplates.State Symbol NativeGuard)
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
      SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap = .done result nextHeap ∧
      (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue heap =
        .done result nextHeap) ∧
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
            setValue selected (.unenumerated (some newHandle) scs)) entry () final)
 := by
  classical
  obtain ⟨found, _lookup, stored, _readState⟩ :=
    (getValue_success readFuel uv before readAfter (.unenumerated (some oldHandle) scs)).mp observed
  obtain ⟨oldValue, oldDecoded, oldAvailable, oldClosed⟩ :=
    realized found.representative oldHandle scs stored
  have oldEncoded : encodeNode oldValue = some oldHandle := by
    exact SourcePruningEnumerationIdentity.lookup_encode heap oldHandle oldValue
      ready.semantic.1.normal.facts.coherent oldDecoded
  have firstFrame : Frame before readAfter := by
    exact (getValue_frame readFuel uv before readAfter (.unenumerated (some oldHandle) scs) total observed).1
  have entryRealized : PendingRealized heap entry := by
    exact realized_preserved heap heap before entry realized (firstFrame.trans entered)
      (SourceEqualityRequiredCache.pure_keeps heap ready)
  by_cases mu : ∃ entry body depthShape ordinaryShape,
    oldValue = .mu entry body depthShape ordinaryShape
  · obtain ⟨muEntry, muBody, muDepthShape, muOrdinaryShape, oldShape⟩ := mu
    refine ⟨oldValue, oldValue, 0, heap, oldHandle, oldDecoded, oldEncoded,
      oldAvailable, oldClosed, ?_, ?_, SourceEqualityRequiredCache.pure_keeps heap ready,
      oldAvailable, oldClosed, oldEncoded, oldDecoded, oldDecoded, firstFrame, entryRealized,
      ?_, ?_, ?_, ?_⟩
    · rw [oldShape]
      rfl
    · intro extra
      rw [oldShape]
      rfl
    · intro survives
      exact survives
    · intro _emptyResult
      simp [Success, reject, ExceptT.run]
    · intro _nonempty _sameHandle
      exact ⟨rfl, (success_pure () () entry entry).mpr ⟨rfl, rfl⟩⟩
    · intro _nonempty changed
      exact False.elim (changed rfl)
  · by_cases inTypes : uv ∈ metadata.types
    · refine ⟨oldValue, oldValue, 0, heap, oldHandle, oldDecoded, oldEncoded,
        oldAvailable, oldClosed, ?_, ?_, SourceEqualityRequiredCache.pure_keeps heap ready,
        oldAvailable, oldClosed, oldEncoded, oldDecoded, oldDecoded, firstFrame, entryRealized,
        ?_, ?_, ?_, ?_⟩
      · exact SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata 0 uv oldValue heap inTypes
      · intro extra
        exact SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata (0 + extra) uv oldValue heap inTypes
      · intro survives
        exact survives
      · intro _emptyResult
        simp [Success, reject, ExceptT.run]
      · intro _nonempty _sameHandle
        exact ⟨rfl, (success_pure () () entry entry).mpr ⟨rfl, rfl⟩⟩
      · intro _nonempty changed
        exact False.elim (changed rfl)
    · have notMu : ∀ entry body depthShape ordinaryShape, oldValue ≠ .mu entry body depthShape ordinaryShape := by
        intro muEntry muBody muDepthShape muOrdinaryShape sameShape
        exact mu ⟨muEntry, muBody, muDepthShape, muOrdinaryShape, sameShape⟩
      obtain ⟨innerOld, result, nativeFuel, nextHeap, newHandle, innerDecoded, _innerEncoded,
          _innerAvailable, _innerClosed, innerNarrowed, innerStable, kept, resultAvailable,
          resultClosed, newEncoded, newDecoded, oldRetained, _innerFrame, innerEntryRealized,
          survivingOld, emptyBranch, equalBranch, changedBranch⟩ :=
        SourcePruningEnumerationNarrowing.narrow_pending_complete fits admits (holeKey metadata.typing uv)
          heap before readAfter entry readFuel uv oldHandle scs ready realized total observed entered
      have oldSame : innerOld = oldValue := by
        exact Option.some.inj (innerDecoded.symm.trans oldDecoded)
      subst innerOld
      have narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap = .done result nextHeap := by
        exact (SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata nativeFuel uv oldValue heap
          notMu inTypes).trans innerNarrowed
      have stable : ∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue heap =
        .done result nextHeap := by
        intro extra
        exact (SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata (nativeFuel + extra) uv oldValue heap
          notMu inTypes).trans (innerStable extra)
      exact ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, oldEncoded,
        oldAvailable, oldClosed, narrowed, stable, kept, resultAvailable, resultClosed,
        newEncoded, newDecoded, oldRetained, firstFrame, innerEntryRealized, survivingOld,
        emptyBranch, equalBranch, changedBranch⟩

end MicroCFTA.SourcePruningEnumerationOuter
