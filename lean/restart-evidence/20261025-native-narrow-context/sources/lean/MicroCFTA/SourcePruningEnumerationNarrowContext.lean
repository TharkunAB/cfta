import MicroCFTA.SourcePruningEnumerationNarrowCache
import MicroCFTA.SourcePruningNativeContext

namespace MicroCFTA.SourcePruningEnumerationNarrowContext
open Cache EnumerationState EnumerationCorrectness EnumerationSchedule
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

/-- One native narrowing result derives its caller, memos and indexed enumeration cache together. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (readAfter : EnumerationState.State Symbol EnumGuard)
    (readFuel uv oldHandle : Nat) (scs : List Suspended) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (read : Success (getValue readFuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter) :
    ∃ (oldValue result : Node) (nativeFuel : Nat) (heap : InternedConstructorTemplates.State Symbol Constraint)
      (newHandle : Nat) (final : Memos),
      let afterCaller := SourceCurrentAllocatedPartialState.advance caller
        (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
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
          Success (reject : EnumerateM Symbol EnumGuard Unit) readAfter () after) ∧
      (result ≠ .empty →
        ∃ (representativeFuel countFuel : Nat) (action : EnumerateM Symbol EnumGuard Unit)
          (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
          SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
            scs oldValue caller.checked.native.machine.heap = .done (result, some action) heap ∧
          Success action readAfter () after.core ∧
          ((newHandle = oldHandle ∧ after = EnumerationExpandableIndex.frame readAfter before) ∨
            (newHandle ≠ oldHandle ∧ ∃ rereadAfter : EnumerationState.State Symbol EnumGuard,
              Success (representative representativeFuel uv) readAfter uv rereadAfter ∧
              Success (setValue uv (.unenumerated (some newHandle) scs)) rereadAfter () after.core ∧
              ∀ extra, SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap (countFuel + extra) uv
                (.unenumerated (some newHandle) scs) scs scs (EnumerationExpandableIndex.frame rereadAfter before) = some after)) ∧
          after.waiting = before.waiting ∧ EnumerationDriver.Ready uv after.core ∧
          Roots after.core.representatives roots ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
          after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
          EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
          (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
          (∀ held, EnumerationReferences.IncomingAvoid held before.core →
            EnumerationReferences.IncomingAvoid held after.core)) := by
  obtain ⟨oldValue, result, nativeFuel, heap, newHandle, oldDecoded, narrowed, stable, _kept,
    resultAvailable, resultClosed, encoded, decoded, rejected, completed⟩ :=
    SourcePruningEnumerationNarrowCache.complete holeKey fits admits metadata caller.checked.native.machine.heap
      before readAfter readFuel uv oldHandle scs roots initial.ready.semantic.ready ready realized paths counts flags read
  obtain ⟨found, _lookup, stored, _readState⟩ :=
    (getValue_success readFuel uv before.core readAfter (.unenumerated (some oldHandle) scs)).mp read
  obtain ⟨old, oldLookup, oldAvailable, _oldClosed⟩ := realized found.representative oldHandle scs stored
  have same : old = oldValue := Option.some.inj (oldLookup.symm.trans oldDecoded)
  subst old
  obtain ⟨final, post, retained, query⟩ := SourcePruningNativeContext.outer_post formulas solver inventory caller memos
    holeKey fits admits metadata nativeFuel uv oldValue result heap initial oldAvailable narrowed
  exact ⟨oldValue, result, nativeFuel, heap, newHandle, final, oldDecoded, narrowed, stable, post,
    retained, query, resultAvailable, resultClosed, encoded, decoded, rejected, completed⟩

end MicroCFTA.SourcePruningEnumerationNarrowContext
