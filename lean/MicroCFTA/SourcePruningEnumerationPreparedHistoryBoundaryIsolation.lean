import MicroCFTA.SourcePruningEnumerationPreparedHistoryReceiptIsolation
import MicroCFTA.SourcePruningEnumerationPrefixIsolatedHistory

/-!
# An original isolated native boundary survives its actual resource history

The input decision is the actual restart decision at the input cache.
Each output retains its own cache and native caller.
Actual native Post receipts retain the decoded boundary handle.
The selected step includes its actual prepared ordinary or opaque arm.
This theorem concerns an original marker. A separate theorem attaches a new head marker.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationDischargeHistory InternedConstructorTemplates EnumerationCorrectness
open SourcePruningEnumerationRecursive (Output)
open SourcePruningEnumerationNodes
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

private theorem restart_row_fields
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata updated : Metadata Typing)
    (before : Cached) (checked core : Core) (next : Option Next)
    (observed : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata before checked) =
      [.ok ((updated, next), core)]) :
    updated = metadata ∧ next = SourcePruningEnumerationRestart.decision stop order metadata before ∧
      core = checked := by
  change (if SourcePruningEnumerationRestart.decision stop order metadata before = some .stuck then []
    else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata before), checked)]) =
      [Except.ok ((updated, next), core)] at observed
  split at observed
  · cases observed
  · have same : metadata = updated ∧
        SourcePruningEnumerationRestart.decision stop order metadata before = next ∧ checked = core := by
      simpa only [List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, and_true, and_assoc] using observed
    exact ⟨same.1.symm, same.2.1.symm, same.2.2.symm⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
variable {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
variable {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
variable {stop : Option (Metadata Typing → Nat → Bool)}
variable {order : Metadata Typing → List Nat → Option Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
variable {metadata : Metadata Typing} {before : Cached} {seed : SourcePruningEnumerationIncomingReservation.Seed}
variable {ceiling : Nat} {next : Option Next} {output : Output (bits + 2) Typing}

/-- Every actual admitted output retains the original isolated boundary at its own native endpoint. -/
theorem ResourceHistory.isolated_boundary
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (held heldHandle : Nat) (value : Node)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    IsolatedPending held heldHandle output.cache.core ∧
      lookupNode output.caller.checked.native.machine.heap heldHandle = some value := by
  induction history generalizing held heldHandle value with
  | stopped _ => exact ⟨isolated, decoded⟩
  | done _ => exact ⟨isolated, decoded⟩
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output admission valid observed _tail ih =>
      have chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) :=
        actualNext.symm
      have prefixIsolated := SourcePruningEnumerationSelectedStep.prefix_isolated
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos held heldHandle value admission.1 isolated decoded boundary chosen valid
      rw [observed] at prefixIsolated
      have full := valid.2.1
      rw [observed] at full
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, cached, same, coreSame,
        _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
      have cacheSame : parked = cached := Option.some.inj same
      subst cached
      have rows : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
          [.ok ((updated, next), core)] := (Option.some.inj rawSame).symm
      obtain ⟨metadataSame, nextSame, returnedCore⟩ := restart_row_fields
        stop order metadata updated parked checked core next rows
      have coreEq : core = parked.core := returnedCore.trans coreSame.symm
      have framed : EnumerationExpandableIndex.frame core parked = parked := by
        rw [coreEq]
        cases parked
        rfl
      have tailNext : next = SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame core parked) := by
        rw [metadataSame, framed]
        exact nextSame
      have tailIsolated : IsolatedPending held heldHandle (EnumerationExpandableIndex.frame core parked).core := by
        rw [framed]
        exact prefixIsolated
      exact ih held heldHandle value tailNext tailIsolated decoded boundary
  | @selected fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      admission valid observed prefixPost _invocation receipt callbackAdmission callback _tail ih =>
      have chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) :=
        actualNext.symm
      have different := EnumerationDischargeHistory.packet_restart_ne formulas solver inventory caller memos metadata before
        held heldHandle uv value stop order admission.1 isolated decoded boundary chosen
      have prefixIsolated := SourcePruningEnumerationSelectedStep.prefix_isolated
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos held heldHandle value admission.1 isolated decoded boundary chosen valid
      rw [observed] at prefixIsolated
      have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      obtain ⟨headIsolated, headPost⟩ := receipt.isolated_post prefixIsolated (Ne.symm different)
      have returnedIsolated := headIsolated.through_recordTypes graph templates workFuel updated uv
        (.inl fragment) headCache.core callbackCore (false, recorded)
        receipt.completed_packet.safe.1.total callbackSuccess
      have fullPost := prefixPost.trans headPost
      have returnedDecoded := lookupNode_keeps _ _ fullPost.effects.keeps heldHandle value decoded
      exact ih held heldHandle value rfl returnedIsolated returnedDecoded boundary

/-- The same output cannot satisfy full structural discharge while that original marker remains. -/
theorem ResourceHistory.not_discharged
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (held heldHandle : Nat) (value : Node)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    ¬SourcePruningEnumerationRendering.Discharged output.cache.core :=
  (history.isolated_boundary held heldHandle value actualNext isolated decoded boundary).1.not_discharged

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
