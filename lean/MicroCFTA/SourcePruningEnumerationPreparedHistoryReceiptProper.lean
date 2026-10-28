import MicroCFTA.SourcePruningEnumerationPreparedHistoryReceiptCanonical
import MicroCFTA.SourcePruningEnumerationPreparedHeadReceiptProper
import MicroCFTA.SourcePruningEnumerationSelectedOpaqueProper

/-!
# Proper storage through one actual prepared selected receipt

Preparation retains the stored values.
Both actual completed branches preserve strict pending paths.
The actual callback retains the same stored values.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationProgress InternedConstructorTemplates
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

/-- The actual selected receipt preserves proper stored suspended tries in either branch. -/
theorem SelectedHistoryReceipt.proper
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (proper : ProperState before.core) : ProperState after.core := by
  obtain ⟨entered, handle, scs, _decoded, _prepared, _heap, _preparationBound,
    _original, _ready, _stored, _preparing, _actual, _lookup, _preparationPost,
    _enteredPacket, _stable, _enteredReady, enteredStored, _counter, values,
    _flags, _waiting, _available, _closed, _language, branches⟩ := receipt
  have enteredProperState : ProperState entered.core := by
    intro value member
    exact proper value (by simpa only [values] using member)
  rcases branches with ordinary | otherBranch
  · obtain ⟨_parentEntry, _edges, _depth, _free, _edge, _headSeed, _inherited,
      _headInventory, _headCaller, _headMemos, _headBound, _prepared,
      _nonterminal, _post, _captured, completed⟩ := ordinary
    exact completed.proper enteredProperState
  · obtain ⟨_gate, running, _post, _captured, _completed, _admitted, _pending, _history⟩ := otherBranch
    have inherited : ProperInputs scs := proper_inputs (.unenumerated (some handle) scs)
      (enteredProperState _ (List.mem_of_getElem? enteredStored))
    exact SourcePruningEnumerationSelectedOpaqueDispatch.complete_proper enteredProperState inherited running

/-- Either actual callback result preserves proper storage after the same selected receipt. -/
theorem SelectedHistoryReceipt.proper_after_callback
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (proper : ProperState before.core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) : ProperState callbackCore := by
  have completedProperState := receipt.proper proper
  have completedPacket := receipt.completed_packet
  have frame := SourcePruningRecordTypes.recordTypes_frame graph templates callbackFuel metadata uv (.inl fragment)
    after.core callbackCore result completedPacket.safe.1.total recorded
  intro value member
  exact completedProperState value (by simpa only [frame.values] using member)

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
