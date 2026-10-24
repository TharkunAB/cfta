import MicroCFTA.SourcePruningEnumerationOuter

namespace MicroCFTA.SourcePruningEnumerationAction
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing Key : Type}

local instance actionMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Narrow once and retain the complete value beside the actual enumeration action. -/
def prepare [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol NativeGuard → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv oldHandle : Nat)
    (scs : List EnumerationState.Suspended) (oldValue : InternedConstructorTemplates.Value Symbol NativeGuard)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) :
    MergedSourceComparison.Result Symbol NativeGuard
      (InternedConstructorTemplates.Value Symbol NativeGuard × Option (EnumerateM Symbol EnumGuard Unit))
 :=
  match SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
  | .failed fault after => .failed fault after
  | .done result nextHeap =>
      .done (result,
        match result with
        | .empty => some reject
        | _ =>
            match encodeNode result with
            | none => none
            | some newHandle =>
                some (
                  if newHandle = oldHandle then
                    pure ()
                  else
                    representative representativeFuel uv >>= fun selected =>
                      setValue selected (.unenumerated (some newHandle) scs))) nextHeap

/-- Connect the computed action to the same actual pending observation and branch states. -/
theorem prepare_pending_complete
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
      (result = .empty → ∀ representativeFuel,
        prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
          .done (result, some (reject : EnumerateM Symbol EnumGuard Unit)) nextHeap ∧
        ¬ ∃ final : EnumerationState.State Symbol EnumGuard,
          Success (reject : EnumerateM Symbol EnumGuard Unit) entry () final) ∧
      (result ≠ .empty → newHandle = oldHandle →
        result = oldValue ∧
        (∀ representativeFuel,
          prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
            .done (result, some (pure () : EnumerateM Symbol EnumGuard Unit)) nextHeap) ∧
        Success (pure () : EnumerateM Symbol EnumGuard Unit) entry () entry) ∧
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
          prepare (EnumGuard := EnumGuard) holeKey fits admits metadata nativeFuel rereadFuel uv oldHandle scs oldValue heap =
            .done (result, some (representative rereadFuel uv >>= fun selected =>
              setValue selected (.unenumerated (some newHandle) scs))) nextHeap ∧
          Success (representative rereadFuel uv >>= fun selected =>
            setValue selected (.unenumerated (some newHandle) scs)) entry () final)
 := by
  obtain ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, oldEncoded,
      oldAvailable, oldClosed, narrowed, stable, kept, resultAvailable, resultClosed,
      newEncoded, newDecoded, oldRetained, firstFrame, entryRealized, survivingOld,
      emptyBranch, equalBranch, changedBranch⟩ :=
    SourcePruningEnumerationOuter.narrow_pending_complete holeKey fits admits metadata
      heap before readAfter entry readFuel uv oldHandle scs ready realized total observed entered
  refine ⟨oldValue, result, nativeFuel, nextHeap, newHandle, oldDecoded, oldEncoded,
    oldAvailable, oldClosed, narrowed, stable, kept, resultAvailable, resultClosed,
    newEncoded, newDecoded, oldRetained, firstFrame, entryRealized, survivingOld, ?_, ?_, ?_⟩
  · intro emptyResult representativeFuel
    refine ⟨?_, emptyBranch emptyResult⟩
    simp only [prepare, narrowed, emptyResult]
  · intro nonempty sameHandle
    obtain ⟨equalValue, equalSuccess⟩ := equalBranch nonempty sameHandle
    refine ⟨equalValue, ?_, equalSuccess⟩
    intro representativeFuel
    cases result with
    | empty => exact False.elim (nonempty rfl)
    | reference name => simp [encodeNode] at newEncoded
    | node nodeEntry edges depth free =>
        simp only [prepare, narrowed, encodeNode, Option.some.inj newEncoded, ite_eq_left sameHandle]
    | union unionEntry members depth free =>
        simp only [prepare, narrowed, encodeNode, Option.some.inj newEncoded, ite_eq_left sameHandle]
    | mu muEntry body depthShape ordinaryShape =>
        simp only [prepare, narrowed, encodeNode, Option.some.inj newEncoded, ite_eq_left sameHandle]
  · intro nonempty changedHandle
    obtain ⟨root, size, rereadFuel, rereadAfter, final, rootPath, secondRead, secondFrame,
        wholeFrame, oldStored, bound, rereadRealized, written, finalShape, finalStored,
        finalRealized, boundRun⟩ := changedBranch nonempty changedHandle
    refine ⟨root, size, rereadFuel, rereadAfter, final, rootPath, secondRead, secondFrame,
      wholeFrame, oldStored, bound, rereadRealized, written, finalShape, finalStored,
      finalRealized, ?_, boundRun⟩
    cases result with
    | empty => exact False.elim (nonempty rfl)
    | reference name => simp [encodeNode] at newEncoded
    | node nodeEntry edges depth free =>
        simp only [prepare, narrowed, encodeNode, Option.some.inj newEncoded, ite_eq_right changedHandle]
    | union unionEntry members depth free =>
        simp only [prepare, narrowed, encodeNode, Option.some.inj newEncoded, ite_eq_right changedHandle]
    | mu muEntry body depthShape ordinaryShape =>
        simp only [prepare, narrowed, encodeNode, Option.some.inj newEncoded, ite_eq_right changedHandle]

end MicroCFTA.SourcePruningEnumerationAction
