import MicroCFTA.SourcePruningEnumerationCapturedKeyAncestry
import MicroCFTA.SourcePruningEnumerationOpaqueKeyAncestry
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationPreparedHistoryReceiptCanonical

/-!
# Original finite key shapes through an actual prepared receipt

The original model derives the key inserted by the actual entry.
Both actual completed receipt branches retain the same history carrier.
The actual recording frame retains both complete ancestry fields.
No model or key-domain supplier at a later state is required.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationOrigins SourcePruningEnumerationKeyAncestry
open SourcePruningEnumerationModelKeyShapes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
variable {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
variable {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
variable {returnedInventory : Inventory} {returnedMemos : Memos}

/-- An original modeled input derives the finite historical shapes at its actual completed receipt. -/
theorem SelectedHistoryReceipt.key_ancestry
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before.core)
    (origins : AssignmentOrigins whole before.core.counter assignment)
    (canonical : EnumerationValidity.Canonical before.core)
    (bounded : KeyAncestry (keyShapes whole) before.core) :
    KeyAncestry (keyShapes whole) after.core := by
  obtain ⟨entered, handle, scs, decoded, _prepared, _heap, _preparationBound,
    original, _ready, _stored, _preparing, actual, _lookup, _preparationPost,
    _enteredPacket, _stable, _enteredReady, _enteredStored, _counter, _values,
    _flags, _waiting, _available, _closed, _language, branches⟩ := receipt
  have entry : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv)
      before.core (uv, handle, scs, decoded) entered.core := by
    have raw := congrArg Prod.fst actual
    change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv
      before.core) = [.ok ((uv, handle, scs, decoded), entered.core)] at raw
    rw [Success, raw]
    exact List.mem_singleton_self _
  have enteredBounded := SourcePruningEnumerationEntry.enter_key_ancestry
    caller.checked.native.machine.heap workFuel uv before.core entered.core uv handle scs decoded
    language meaning whole assignment satisfied origins canonical original.safe.1.aligned bounded entry
  rcases branches with ordinary | otherBranch
  · obtain ⟨_parentEntry, _edges, _depth, _free, _edge, _headSeed, _inherited,
      _headInventory, _headCaller, _headMemos, _headBound, _prepared,
      _nonterminal, _post, captured, _completed⟩ := ordinary
    exact SourcePruningEnumerationCapturedEdge.observed_cache_key_ancestry enteredBounded captured
  · obtain ⟨_gate, running, _post, _captured, _completed, _admitted, _pending, _history⟩ := otherBranch
    exact SourcePruningEnumerationSelectedOpaqueDispatch.complete_key_ancestry enteredBounded running

/-- The same actual recording result retains the original finite historical key shapes. -/
theorem SelectedHistoryReceipt.key_ancestry_after_callback
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before.core)
    (origins : AssignmentOrigins whole before.core.counter assignment)
    (canonical : EnumerationValidity.Canonical before.core)
    (bounded : KeyAncestry (keyShapes whole) before.core)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) : KeyAncestry (keyShapes whole) callbackCore := by
  have completedBounded := receipt.key_ancestry language meaning whole assignment
    satisfied origins canonical bounded
  have completedPacket := receipt.completed_packet
  have framed := SourcePruningRecordTypes.recordTypes_frame graph templates callbackFuel metadata uv (.inl fragment)
    after.core callbackCore result completedPacket.safe.1.total recorded
  exact completedBounded.frame framed

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
