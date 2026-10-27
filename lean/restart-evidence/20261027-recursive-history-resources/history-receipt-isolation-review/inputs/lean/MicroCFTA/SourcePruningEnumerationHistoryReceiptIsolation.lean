import MicroCFTA.SourcePruningEnumerationFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationIsolationReads
import MicroCFTA.SourcePruningEnumerationCapturedIsolation

/-!
# Isolation through one actual ordinary history receipt

The original slot survives actual entry and completed capture.
The callback retains that slot at its actual returned core.
The isolated slot must differ from the current captured target.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open EnumerationDischargeHistory
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
variable {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
variable {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
variable {returnedInventory : Inventory} {returnedMemos : Memos} {held heldHandle : Nat}

/-- The exact entry and head receipts retain a different original isolated slot. -/
theorem OrdinaryHistoryReceipt.isolated
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (isolated : IsolatedPending held heldHandle before.core) (different : held ≠ uv) :
    IsolatedPending held heldHandle after.core := by
  obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited,
    headInventory, headCaller, headMemos, headBound,
    original, entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have enteredIsolated := isolated.through_entry_row caller.checked.native.machine.heap workFuel uv
    before.core entered.core held heldHandle uv handle scs decoded original.safe.1.total entry
  exact completed.isolated enteredIsolated different

/-- Either actual callback result retains the slot after the same completed history receipt. -/
theorem OrdinaryHistoryReceipt.isolated_after_callback
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (isolated : IsolatedPending held heldHandle before.core) (different : held ≠ uv)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) :
    IsolatedPending held heldHandle callbackCore := by
  have capturedIsolated := receipt.isolated isolated different
  obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited,
    headInventory, headCaller, headMemos, headBound,
    _original, _entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  exact capturedIsolated.through_recordTypes graph templates callbackFuel metadata uv (.inl fragment)
    after.core callbackCore result completed.completed.safe.1.total recorded

end MicroCFTA.SourcePruningEnumerationRecursive
