import MicroCFTA.SourcePruningEnumerationCreatedIsolation
import MicroCFTA.SourcePruningEnumerationPreparedHistoryBoundaryIsolation

/-!
# Attach an actual parking event to its remaining output history

The selected prefix creates the marker at its existing selected root.
The exact restart singleton supplies the tail cache, metadata and decision.
The tail retains that marker at the same output's own native endpoint.
No marker from a different sibling or head is attached by this theorem.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open SourcePruningEnumerationRecursive (Packet Output)
open EnumerationState EnumerationCorrectness EnumerationDischargeHistory
open InternedConstructorTemplates SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

private theorem repeated_native_boundary
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv handle : Nat)
    (scs : List Suspended) (before after : Core)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before true after) :
    ∃ value, lookupNode heap handle = some value ∧ MergedOrdinaryHeight.recursiveBoundary value = true := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · exact ⟨value, rfl, boundary⟩
      · have impossible : Success (pure false) before true after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
            Bool.false_eq_true, ↓reduceIte] using observed
        obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
        cases impossible

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual parked prefix creates an isolated marker that survives its own remaining admitted history. -/
theorem parked_tail_created_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel recursiveFuel : Nat) (inventory : Inventory) (caller : Caller (bits + 2))
    (memos : Memos) (metadata updated : Metadata Typing) (before parked : Cached)
    (uv : Nat) (checked core : Core) (next : Option Next)
    (tailSeed : SourcePruningEnumerationIncomingReservation.Seed) (tailCeiling : Nat)
    (output : Output (bits + 2) Typing)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata formulas solver inventory workFuel uv caller before memos
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query))
    (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .parked checked (some parked) (some [.ok ((updated, next), core)]))
    (tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos updated (EnumerationExpandableIndex.frame core parked)
        tailSeed tailCeiling next output) :
    ∃ handle bucket value,
      before.core.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      IsolatedPending uv handle parked.core ∧ IsolatedPending uv handle output.cache.core ∧
      lookupNode output.caller.checked.native.machine.heap handle = some value ∧
      ¬SourcePruningEnumerationRendering.Discharged output.cache.core := by
  obtain ⟨ready, incoming, _selectedValue⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv packet.valid packet.safe chosen
  have full := valid.2.1
  rw [observed] at full
  obtain ⟨handle, bucket, readAfter, reading, checking, cached, same, coreSame,
    _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
  have cacheSame : parked = cached := Option.some.inj same
  subst cached
  have readSuccess : Success (getValue workFuel uv) before.core
      (.unenumerated (some handle) bucket) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  have frame := (EnumerationCompressionFrame.getValue_frame workFuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
  have readReady := (EnumerationDriver.getValue_ready workFuel uv before.core readAfter _ ready readSuccess).1
  have readStored := (EnumerationDriver.getValue_root workFuel uv before.core readAfter _
    ready.safe ready.inside ready.root readSuccess).2.2.2
  have stored : before.core.values[uv]? = some (.unenumerated (some handle) bucket) := by
    simpa only [frame.values] using readStored
  have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap workFuel uv handle bucket) readAfter true checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  obtain ⟨value, decoded, boundary⟩ := repeated_native_boundary caller.checked.native.machine.heap
    workFuel uv handle bucket readAfter checked checkSuccess
  have created := checkRepeated_created_isolated caller.checked.native.machine.heap workFuel uv handle bucket
    readAfter checked readReady
    (EnumerationPendingReplacement.frame_incoming uv before.core readAfter frame incoming) checkSuccess
  have parkedIsolated : IsolatedPending uv handle parked.core := by
    rw [coreSame]
    exact created
  have rows : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
      [.ok ((updated, next), core)] := (Option.some.inj rawSame).symm
  have actual := rows
  rw [← coreSame] at actual
  change (if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
      else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), parked.core)]) =
      [Except.ok ((updated, next), core)] at actual
  split at actual
  · cases actual
  · have fields : metadata = updated ∧
        SourcePruningEnumerationRestart.decision stop order metadata parked = next ∧ parked.core = core := by
      simpa only [List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, and_true, and_assoc] using actual
    have framed : EnumerationExpandableIndex.frame core parked = parked := by
      rw [← fields.2.2]
      cases parked
      rfl
    have tailNext : next = SourcePruningEnumerationRestart.decision stop order updated
        (EnumerationExpandableIndex.frame core parked) := by
      rw [← fields.1, framed]
      exact fields.2.1.symm
    have tailIsolated : IsolatedPending uv handle (EnumerationExpandableIndex.frame core parked).core := by
      rw [framed]
      exact parkedIsolated
    obtain ⟨retained, finalDecoded⟩ := tail.isolated_boundary uv handle value tailNext tailIsolated decoded boundary
    exact ⟨handle, bucket, value, stored, decoded, boundary, parkedIsolated, retained,
      finalDecoded, retained.not_discharged⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
