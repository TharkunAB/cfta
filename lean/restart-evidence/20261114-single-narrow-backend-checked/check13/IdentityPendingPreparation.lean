import MicroCFTA.SourcePruningEnumerationAction

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationAction
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing : Type}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Identity preparation retains the actual pending value, handle and native heap. -/
private theorem prepare_identity_pending_complete
    (metadata : Metadata Typing)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before readAfter entry : EnumerationState.State Symbol EnumGuard)
    (readFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (ready : SourceEqualityRequiredCache.Ready heap) (realized : PendingRealized heap before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (entered : Frame readAfter entry) :
    ∃ oldValue : InternedConstructorTemplates.Value Symbol NativeGuard,
      lookupNode heap oldHandle = some oldValue ∧ encodeNode oldValue = some oldHandle ∧
      Available heap oldValue ∧ oldValue.free = [] ∧
      SourceEqualityRequiredCache.Keeps heap heap ∧
      Frame before readAfter ∧ PendingRealized heap entry ∧
      (EnumerationReferences.PendingReferences before → EnumerationReferences.PendingReferences entry) ∧
      (∀ held, EnumerationReferences.IncomingAvoid held before → EnumerationReferences.IncomingAvoid held entry) ∧
      (oldValue = .empty → ∀ nativeFuel representativeFuel,
        prepareWithNarrow (EnumGuard := EnumGuard) (fun _ _ _ value heap => .done value heap)
          metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
            .done (oldValue, some (reject : EnumerateM Symbol EnumGuard Unit)) heap ∧
        ExceptT.run ((reject : EnumerateM Symbol EnumGuard Unit) entry) = []) ∧
      (oldValue ≠ .empty → ∀ nativeFuel representativeFuel,
        prepareWithNarrow (EnumGuard := EnumGuard) (fun _ _ _ value heap => .done value heap)
          metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
            .done (oldValue, some (pure () : EnumerateM Symbol EnumGuard Unit)) heap ∧
        ExceptT.run ((pure () : EnumerateM Symbol EnumGuard Unit) entry) = [.ok ((), entry)]) := by
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
  have kept : SourceEqualityRequiredCache.Keeps heap heap :=
    SourceEqualityRequiredCache.pure_keeps heap ready
  have entryRealized : PendingRealized heap entry := by
    exact realized_preserved heap heap before entry realized (firstFrame.trans entered) kept
  refine ⟨oldValue, oldDecoded, oldEncoded, oldAvailable, oldClosed, kept, firstFrame, entryRealized,
    EnumerationPendingReplacement.frame_pending before entry (firstFrame.trans entered),
    (fun held => EnumerationPendingReplacement.frame_incoming held before entry (firstFrame.trans entered)),
    ?_, ?_⟩
  · intro emptyValue nativeFuel representativeFuel
    constructor
    · simp only [prepareWithNarrow, emptyValue]
    · rfl
  · intro nonempty nativeFuel representativeFuel
    constructor
    · cases oldValue with
      | empty => exact False.elim (nonempty rfl)
      | reference name => simp [encodeNode] at oldEncoded
      | node nodeEntry edges depth free =>
          simp only [prepareWithNarrow, oldEncoded, if_pos rfl]
      | union unionEntry members depth free =>
          simp only [prepareWithNarrow, oldEncoded, if_pos rfl]
      | mu muEntry body depthShape ordinaryShape =>
          simp only [prepareWithNarrow, oldEncoded, if_pos rfl]
    · rfl

end MicroCFTA.SourcePruningEnumerationAction

#print axioms MicroCFTA.SourcePruningEnumerationAction.prepare_identity_pending_complete
