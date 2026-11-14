import MicroCFTA.SourcePruningEnumerationSelectedStep

set_option autoImplicit false

/-!
# Identity narrowing for actual pending reads

The preparation law retains the selected value, handle and native heap.
The prefix law retains the actual non-repeated observations and caller advance.
Both laws use the same pending read.
-/

namespace MicroCFTA.SourcePruningEnumerationAction
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing : Type}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Identity preparation retains the actual pending value, handle and native heap. -/
theorem prepare_identity_pending_complete
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
          simp only [prepareWithNarrow, oldEncoded, ite_true]
      | union unionEntry members depth free =>
          simp only [prepareWithNarrow, oldEncoded, ite_true]
      | mu muEntry body depthShape ordinaryShape =>
          simp only [prepareWithNarrow, oldEncoded, ite_true]
    · rfl

end MicroCFTA.SourcePruningEnumerationAction


namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Identity narrowing retains the exact non-repeated selected prefix. -/
theorem runPrefix_identity_pending
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (readFuel checkFuel uv oldHandle : Nat) (scs : List Suspended)
    (readAfter checked : Core)
    (ready : SourceEqualityRequiredCache.Ready caller.checked.native.machine.heap)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (total : UnionFind.Total before.core.representatives)
    (reading : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (entered : Frame readAfter checked) :
    ∃ oldValue : Node,
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      encodeNode oldValue = some oldHandle ∧
      Available caller.checked.native.machine.heap oldValue ∧ oldValue.free = [] ∧
      (oldValue = .empty → ∀ nativeFuel representativeFuel indexFuel callbackFuel,
        runPrefixWithNarrow (fun _ _ _ value heap => .done value heap)
          graph templates stop order metadata readFuel checkFuel nativeFuel representativeFuel
          indexFuel callbackFuel uv caller before queries =
        .narrowed checked
          (.done (oldValue, some (reject : EnumerateM Symbol Constraint Unit)) caller.checked.native.machine.heap)
          (SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
            caller.fourth caller.merge)
          queries (some []) none none none) ∧
      (oldValue ≠ .empty → ∀ nativeFuel representativeFuel indexFuel callbackFuel,
        runPrefixWithNarrow (fun _ _ _ value heap => .done value heap)
          graph templates stop order metadata readFuel checkFuel nativeFuel representativeFuel
          indexFuel callbackFuel uv caller before queries =
        .narrowed checked
          (.done (oldValue, some (pure () : EnumerateM Symbol Constraint Unit)) caller.checked.native.machine.heap)
          (SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
            caller.fourth caller.merge)
          queries (some [.ok ((), checked)]) (some (EnumerationExpandableIndex.frame checked before))
            (some [.ok ((false, metadata), checked)]) none) := by
  have observed : Success (getValue readFuel uv) before.core
      (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  obtain ⟨oldValue, decoded, encoded, available, closed, _kept, _firstFrame, _entryRealized,
      _pending, _incoming, emptyBranch, nonemptyBranch⟩ :=
    SourcePruningEnumerationAction.prepare_identity_pending_complete metadata
      caller.checked.native.machine.heap before.core readAfter checked readFuel uv oldHandle scs
      ready realized total observed entered
  refine ⟨oldValue, decoded, encoded, available, closed, ?_, ?_⟩
  · intro emptyValue nativeFuel representativeFuel indexFuel callbackFuel
    obtain ⟨prepared, raw⟩ := emptyBranch emptyValue nativeFuel representativeFuel
    simp only [runPrefixWithNarrow, reading, checking, decoded, prepared, raw] <;> rfl
  · intro nonempty nativeFuel representativeFuel indexFuel callbackFuel
    obtain ⟨prepared, raw⟩ := nonemptyBranch nonempty nativeFuel representativeFuel
    have adapted : SourcePruningEnumerationNarrowAdapter.adapt caller.checked.native.machine.heap
        indexFuel uv oldHandle oldHandle scs before checked =
          some (EnumerationExpandableIndex.frame checked before) := by
      simp only [SourcePruningEnumerationNarrowAdapter.adapt, ite_true]
    have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates callbackFuel
        metadata uv (.inr oldHandle) (EnumerationExpandableIndex.frame checked before).core) =
          [.ok ((false, metadata), checked)] := by
      rw [SourcePruningRecordTypes.recordTypes_inr]
      rfl
    simp only [runPrefixWithNarrow, reading, checking, decoded, prepared, raw, encoded,
      adapted, recorded] <;> rfl

end MicroCFTA.SourcePruningEnumerationSelectedStep

