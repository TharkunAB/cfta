import MicroCFTA.SourcePruningEnumerationIdentityPrefix
import MicroCFTA.SourcePruningEnumerationRecursionOrder

set_option autoImplicit false

/-!
# A common bound for the identity selected prefix

The original selection invariants supply the read and recursion-check observations.
One bound covers the repeated and non-repeated cases at every larger fuel.
The result retains the actual caller, cache and endpoint queries.
-/

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
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

/-- Original selected-root conditions derive one common identity prefix bound. -/
theorem runPrefix_identity_selected_complete
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (nativeReady : SourceEqualityRequiredCache.Ready caller.checked.native.machine.heap)
    (safe : Safe before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (fuel handle : Nat) (scs : List Suspended) (value : Node)
      (readAfter : Core) (repeated : Bool) (after : Cached),
      before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      encodeNode value = some handle ∧
      Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
      (∀ extra, ExceptT.run (getValue (fuel + extra) uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap (fuel + extra) uv handle scs readAfter) =
          [.ok (repeated, after.core)]) ∧
      Frame before.core readAfter ∧
      EnumerationDriver.Ready uv after.core ∧ Roots after.core.representatives roots ∧
      PendingRealized caller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumerationReferences.IncomingAvoid uv after.core ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      ∀ extra nativeFuel representativeFuel callbackFuel,
        (repeated = true →
          runPrefixWithNarrow (fun _ _ _ incoming heap => .done incoming heap)
            graph templates stop order metadata (fuel + extra) (fuel + extra) nativeFuel representativeFuel
            (fuel + extra) callbackFuel uv caller before queries =
          .parked after.core (some after)
            (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata after after.core)))) ∧
        (repeated = false →
          (value = .empty →
            runPrefixWithNarrow (fun _ _ _ incoming heap => .done incoming heap)
              graph templates stop order metadata (fuel + extra) (fuel + extra) nativeFuel representativeFuel
              (fuel + extra) callbackFuel uv caller before queries =
            .narrowed after.core
              (.done (value, some (reject : EnumerateM Symbol Constraint Unit)) caller.checked.native.machine.heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
                caller.fourth caller.merge)
              queries (some []) none none none) ∧
          (value ≠ .empty →
            runPrefixWithNarrow (fun _ _ _ incoming heap => .done incoming heap)
              graph templates stop order metadata (fuel + extra) (fuel + extra) nativeFuel representativeFuel
              (fuel + extra) callbackFuel uv caller before queries =
            .narrowed after.core
              (.done (value, some (pure () : EnumerateM Symbol Constraint Unit)) caller.checked.native.machine.heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
                caller.fourth caller.merge)
              queries (some [.ok ((), after.core)]) (some after)
                (some [.ok ((false, metadata), after.core)]) none)) := by
  obtain ⟨readFuel, handle, scs, value, readAfter, checkFuel, repeated, after,
      stored, decoded, available, closed, reads, readFrame, checks, afterReady, afterPaths,
      afterRealized, afterCounts, afterFlags, incoming, pending, continued, parked⟩ :=
    SourcePruningEnumerationRecursion.selected_complete caller.checked.native.machine.heap
      before preference uv roots safe selection realized paths counts flags
  have encoded : encodeNode value = some handle :=
    SourcePruningEnumerationIdentity.lookup_encode caller.checked.native.machine.heap handle value
      nativeReady.semantic.1.normal.facts.coherent decoded
  have indexComplete : ∃ indexFuel, repeated = true → ∀ extra,
      SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap (indexFuel + extra)
        uv handle scs before after.core = some after := by
    cases repeated with
    | false =>
        refine ⟨0, ?_⟩
        intro impossible
        cases impossible
    | true =>
        obtain ⟨_boundary, _cleared, _disabled, _waiting, resolved, indexFuel, _frame,
            _root, _seen, written, indexed⟩ := parked rfl
        refine ⟨indexFuel, ?_⟩
        intro _ extra
        exact SourcePruningEnumerationParkedRestart.adapt_after_write caller.checked.native.machine.heap
          (indexFuel + extra) uv handle scs before after resolved after.core written (indexed extra) rfl
  obtain ⟨indexFuel, indexed⟩ := indexComplete
  let fuel := readFuel + checkFuel + indexFuel
  have readUniform (extra : Nat) : ExceptT.run (getValue (fuel + extra) uv before.core) =
      [.ok (.unenumerated (some handle) scs, readAfter)] := by
    simpa only [fuel, Nat.add_assoc] using reads (checkFuel + indexFuel + extra)
  have checkUniform (extra : Nat) : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap (fuel + extra) uv handle scs readAfter) =
        [.ok (repeated, after.core)] := by
    simpa only [fuel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      checks (readFuel + indexFuel + extra)
  refine ⟨fuel, handle, scs, value, readAfter, repeated, after, stored, decoded, encoded,
    available, closed, readUniform, checkUniform, readFrame, afterReady, afterPaths,
    afterRealized, afterCounts, afterFlags, incoming, pending, ?_⟩
  intro extra nativeFuel representativeFuel callbackFuel
  constructor
  · intro repeatedTrue
    have adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
        (fuel + extra) uv handle scs before after.core = some after := by
      simpa only [fuel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        indexed repeatedTrue (readFuel + checkFuel + extra)
    simp only [runPrefixWithNarrow, readUniform extra, checkUniform extra, repeatedTrue,
      adapted, Option.map_some]
  · intro repeatedFalse
    have falseCheck : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap (fuel + extra) uv handle scs readAfter) =
          [.ok (false, after.core)] := by
      simpa only [repeatedFalse] using checkUniform extra
    have checked : Success (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap (fuel + extra) uv handle scs) readAfter false after.core := by
      rw [Success, falseCheck]
      exact List.mem_singleton_self _
    have entered : Frame readAfter after.core :=
      SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame caller.checked.native.machine.heap
        (fuel + extra) uv handle scs readAfter after.core (readFrame.total safe.1.total) checked
    obtain ⟨_frame, sameFlags, sameWaiting, _stored⟩ := continued repeatedFalse
    have sameCache : EnumerationExpandableIndex.frame after.core before = after := by
      cases before with
      | mk beforeCore beforeFlags beforeWaiting =>
          cases after with
          | mk afterCore afterFlags afterWaiting =>
              dsimp only at sameFlags sameWaiting
              cases sameFlags
              cases sameWaiting
              rfl
    obtain ⟨innerValue, innerDecoded, _innerEncoded, _innerAvailable, _innerClosed,
        emptyBranch, nonemptyBranch⟩ :=
      runPrefix_identity_pending graph templates stop order metadata caller before queries
        (fuel + extra) (fuel + extra) uv handle scs readAfter after.core nativeReady
        realized safe.1.total (readUniform extra) falseCheck entered
    have sameValue : innerValue = value := Option.some.inj (innerDecoded.symm.trans decoded)
    subst innerValue
    constructor
    · intro emptyValue
      exact emptyBranch emptyValue nativeFuel representativeFuel (fuel + extra) callbackFuel
    · intro nonempty
      simpa only [sameCache] using
        nonemptyBranch nonempty nativeFuel representativeFuel (fuel + extra) callbackFuel

end MicroCFTA.SourcePruningEnumerationSelectedStep
