import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationPreparedHeadReceiptCanonical
import MicroCFTA.SourcePruningEnumerationSelectedOpaqueCanonical

/-!
# Canonical storage through one actual prepared selected receipt

The actual preparation retains the complete stored value list.
Both completed receipt branches preserve canonical storage.
The actual callback retains the same stored values.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
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

/-- Either actual completed receipt retains its own full output packet. -/
theorem SelectedHistoryReceipt.completed_packet
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos) :
    Packet formulas solver returnedInventory reached returnedMemos metadata after := by
  obtain ⟨_entered, _handle, _scs, _decoded, _prepared, _heap, _preparationBound,
    _original, _ready, _stored, _preparing, _actual, _lookup, _preparationPost,
    _enteredPacket, _stable, _enteredReady, _enteredStored, _counter, _values,
    _flags, _waiting, _available, _closed, _language, branches⟩ := receipt
  rcases branches with ordinary | otherBranch
  · obtain ⟨_parentEntry, _edges, _depth, _free, _edge, _headSeed, _inherited,
      _headInventory, _headCaller, _headMemos, _headBound, _prepared,
      _nonterminal, _post, _captured, completed⟩ := ordinary
    exact completed.completed
  · obtain ⟨_gate, _running, _post, _captured, completed, _admitted, _pending, _history⟩ := otherBranch
    exact completed

/-- The actual selected receipt preserves canonical stored suspended tries in either branch. -/
theorem SelectedHistoryReceipt.canonical
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (canonical : Canonical before.core) : Canonical after.core := by
  obtain ⟨entered, _handle, scs, _decoded, _prepared, _heap, _preparationBound,
    _original, _ready, _stored, _preparing, _actual, _lookup, _preparationPost,
    _enteredPacket, _stable, _enteredReady, enteredStored, _counter, values,
    _flags, _waiting, _available, _closed, _language, branches⟩ := receipt
  have enteredCanonical : Canonical entered.core := by
    intro value member
    exact canonical value (by simpa only [values] using member)
  rcases branches with ordinary | otherBranch
  · obtain ⟨_parentEntry, _edges, _depth, _free, _edge, _headSeed, _inherited,
      _headInventory, _headCaller, _headMemos, _headBound, _prepared,
      _nonterminal, _post, _captured, completed⟩ := ordinary
    exact completed.canonical enteredCanonical
  · obtain ⟨_gate, running, _post, _captured, _completed, _admitted, _pending, _history⟩ := otherBranch
    have inherited : ValidSuspended scs := enteredCanonical _ (List.mem_of_getElem? enteredStored)
    exact SourcePruningEnumerationSelectedOpaqueDispatch.complete_canonical enteredCanonical inherited running

/-- Either actual callback result preserves canonical storage after the same selected receipt. -/
theorem SelectedHistoryReceipt.canonical_after_callback
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (canonical : Canonical before.core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) : Canonical callbackCore := by
  have completedCanonical := receipt.canonical canonical
  have completedPacket := receipt.completed_packet
  have frame := SourcePruningRecordTypes.recordTypes_frame graph templates callbackFuel metadata uv (.inl fragment)
    after.core callbackCore result completedPacket.safe.1.total recorded
  intro value member
  exact completedCanonical value (by simpa only [frame.values] using member)

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
