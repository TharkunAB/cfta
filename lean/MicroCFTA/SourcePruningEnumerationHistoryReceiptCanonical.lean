import MicroCFTA.SourcePruningEnumerationFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationHeadReceiptCanonical
import MicroCFTA.SourcePruningEnumerationEntryCanonical

/-!
# Canonical storage through an actual ordinary history receipt

Actual entry preserves the original stored tries.
The completed head uses the same entered cache.
The actual callback preserves the completed stored values.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
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
variable {returnedInventory : Inventory} {returnedMemos : Memos}

/-- Actual entry and its completed head preserve canonical storage. -/
theorem OrdinaryHistoryReceipt.canonical
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (canonical : Canonical before.core) : Canonical after.core := by
  obtain ⟨entered, handle, scs, decoded, _edge, _headSeed, _inherited,
    _headInventory, _headCaller, _headMemos, _headBound,
    _original, entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv)
      before.core (uv, handle, scs, decoded) entered.core := by
    rw [Success, entry]
    exact List.mem_singleton_self _
  have enteredCanonical := (SourcePruningEnumerationEntry.enter_canonical caller.checked.native.machine.heap
    workFuel uv before.core entered.core uv handle scs decoded canonical entrySuccess).1
  exact completed.canonical enteredCanonical

/-- Either actual callback result preserves the same completed canonical storage. -/
theorem OrdinaryHistoryReceipt.canonical_after_callback
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (canonical : Canonical before.core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) : Canonical callbackCore := by
  have completedCanonical := receipt.canonical canonical
  obtain ⟨_entered, _handle, _scs, _decoded, _edge, _headSeed, _inherited,
    _headInventory, _headCaller, _headMemos, _headBound,
    _original, _entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have frame := SourcePruningRecordTypes.recordTypes_frame graph templates callbackFuel metadata uv
    (.inl fragment) after.core callbackCore result completed.completed.safe.1.total recorded
  intro value member
  exact completedCanonical value (by simpa only [frame.values] using member)

end MicroCFTA.SourcePruningEnumerationRecursive
