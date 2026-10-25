import MicroCFTA.SourcePruningEnumerationRecursion
import MicroCFTA.SourcePruningEnumerationNarrowContext

namespace MicroCFTA.SourcePruningEnumerationSelectedNarrow
open Cache EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {EnumGuard Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Original selection derives one read, the native guard, narrowing and the pure Right callback. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (graph : Graph Symbol EnumGuard) (templates : List (Template.Pattern Symbol))
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (readFuel oldHandle : Nat) (scs : List Suspended) (oldValue : Node)
      (readAfter : EnumerationState.State Symbol EnumGuard) (checkFuel : Nat) (repeated : Bool)
      (checked : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      Available caller.checked.native.machine.heap oldValue ∧ oldValue.free = [] ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        (checkFuel + extra) uv oldHandle scs readAfter) = [.ok (repeated, checked.core)]) ∧
      EnumerationDriver.Ready uv checked.core ∧ Roots checked.core.representatives roots ∧
      PendingRealized caller.checked.native.machine.heap checked.core ∧
      EnumerationCanonicalWaiting.Correct roots checked.core.values checked.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((checked.core.values[slot]?).getD .eliminated) = some (checked.expandable slot)) ∧
      EnumerationReferences.IncomingAvoid uv checked.core ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences checked.core) ∧
      (repeated = true → MergedOrdinaryHeight.recursiveBoundary oldValue = true ∧
        checked.core.values[uv]? = some (.unenumerated (some oldHandle) []) ∧ checked.expandable uv = false ∧
        checked.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
        ∃ (resolved : EnumerationState.State Symbol EnumGuard) (countFuel : Nat),
          Frame before.core resolved ∧ Success (representative checkFuel uv) readAfter uv resolved ∧
          recursionKey oldHandle scs ∈ resolved.recursionAncestry uv ∧
          Success (setValue uv (.unenumerated (some oldHandle) [])) resolved () checked.core ∧
          ∀ extra, SourcePruningEnumerationNativeIndex.write caller.checked.native.machine.heap
            (countFuel + extra) uv (.unenumerated (some oldHandle) []) [] scs
              (EnumerationExpandableIndex.frame resolved before) = some checked) ∧
      (repeated = false →
        ∃ (result : Node) (nativeFuel : Nat) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (newHandle : Nat) (final : Memos),
          let afterCaller := SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge
          SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue caller.checked.native.machine.heap =
            .done result heap ∧
          (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue
            caller.checked.native.machine.heap = .done result heap) ∧
          Post formulas solver inventory caller afterCaller final ∧
          Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
          Available afterCaller.checked.native.machine.heap result ∧ result.free = [] ∧
          encodeNode result = some newHandle ∧ lookupNode afterCaller.checked.native.machine.heap newHandle = some result ∧
          (result = .empty → ∀ representativeFuel,
            SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
              scs oldValue caller.checked.native.machine.heap =
              .done (result, some (reject : EnumerateM Symbol EnumGuard Unit)) heap ∧
            ¬ ∃ after : EnumerationState.State Symbol EnumGuard,
              Success (reject : EnumerateM Symbol EnumGuard Unit) checked.core () after) ∧
          (result ≠ .empty →
            ∃ (representativeFuel countFuel : Nat) (action : EnumerateM Symbol EnumGuard Unit)
              (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
              SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
                scs oldValue caller.checked.native.machine.heap = .done (result, some action) heap ∧
              Success action checked.core () after.core ∧
              ((newHandle = oldHandle ∧ after = EnumerationExpandableIndex.frame checked.core before) ∨
                (newHandle ≠ oldHandle ∧ ∃ rereadAfter : EnumerationState.State Symbol EnumGuard,
                  Success (representative representativeFuel uv) checked.core uv rereadAfter ∧
                  Success (setValue uv (.unenumerated (some newHandle) scs)) rereadAfter () after.core ∧
                  ∀ extra, SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
                    (countFuel + extra) uv (.unenumerated (some newHandle) scs) scs scs
                      (EnumerationExpandableIndex.frame rereadAfter before) = some after)) ∧
              after.waiting = before.waiting ∧ EnumerationDriver.Ready uv after.core ∧
              Roots after.core.representatives roots ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
              after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
              EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
              (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
                ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
              (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
              EnumerationReferences.IncomingAvoid uv after.core ∧
              ∀ callbackFuel, Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inr newHandle))
                after.core (false, metadata) after.core)) := by
  have ready := SourcePruningEnumerationSelection.ready caller.checked.native.machine.heap before preference uv
    safe roots paths counts flags selection
  have incoming := SourcePruningEnumerationSelection.incoming caller.checked.native.machine.heap before preference uv
    safe roots paths counts flags selection
  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    oldAvailable, oldClosed, readExact, readFrame, checkExact, checkReady, checkPaths, checkRealized,
    checkCounts, checkFlags, checkIncoming, checkPending, continued, parked⟩ :=
    SourcePruningEnumerationRecursion.selected_complete caller.checked.native.machine.heap before preference uv roots
      safe selection realized paths counts flags
  refine ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    oldAvailable, oldClosed, readExact, checkExact, checkReady, checkPaths, checkRealized, checkCounts,
    checkFlags, checkIncoming, checkPending, parked, ?_⟩
  intro notRepeated
  have entered : Frame readAfter checked.core := readFrame.symm.trans (continued notRepeated).1
  have read : Success (getValue readFuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, ← Nat.add_zero readFuel, readExact 0]
    exact List.mem_singleton_self _
  obtain ⟨old, result, nativeFuel, heap, newHandle, final, decodedOld, narrowed, stable, post, retained,
    query, available, closed, encoded, decoded, rejected, completed⟩ :=
    SourcePruningEnumerationNarrowContext.complete_after_frame formulas solver inventory caller memos
      holeKey fits admits metadata before readAfter checked.core readFuel uv oldHandle scs roots
      initial ready realized paths counts flags read entered checkReady
  have same : old = oldValue := Option.some.inj (decodedOld.symm.trans oldDecoded)
  subst old
  refine ⟨result, nativeFuel, heap, newHandle, final, narrowed, stable, post, retained, query,
    available, closed, encoded, decoded, rejected, ?_⟩
  intro nonempty
  obtain ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
    afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming⟩ := completed nonempty
  refine ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
    afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming uv incoming, ?_⟩
  intro callbackFuel
  rw [SourcePruningRecordTypes.recordTypes_inr]
  exact (success_pure (false, metadata) (false, metadata) after.core after.core).mpr ⟨rfl, rfl⟩

end MicroCFTA.SourcePruningEnumerationSelectedNarrow
