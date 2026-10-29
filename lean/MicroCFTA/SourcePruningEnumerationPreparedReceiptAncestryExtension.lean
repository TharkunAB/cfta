import MicroCFTA.SourcePruningEnumerationPreparedHeadAncestryExtension
import MicroCFTA.SourcePruningEnumerationOpaqueAncestryExtension
import MicroCFTA.SourcePruningEnumerationBoundaryEntryBudget
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationPreparedHistoryReceiptCanonical

/-!
# Per-slot ancestry through an actual prepared receipt

Entry retains the original per-slot recursion histories.
The actual ordinary or opaque completion extends those same histories.
The actual recording frame retains the completed per-slot histories.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationAncestryExtension
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

/-- The actual prepared receipt retains every original key at every slot. -/
theorem SelectedHistoryReceipt.ancestry_extension
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos) :
    Extends before.core after.core := by
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
  obtain ⟨_size, _path, _decoded, histories, _expansion⟩ :=
    SourcePruningEnumerationEntry.enter_history caller.checked.native.machine.heap workFuel uv
      before.core entered.core uv handle scs decoded original.safe.1.total entry
  have enteredExtends : Extends before.core entered.core := by
    intro slot key member
    simpa only [histories] using member
  rcases branches with ordinary | otherBranch
  · obtain ⟨_parentEntry, _edges, _depth, _free, _edge, _headSeed, _inherited,
      _headInventory, _headCaller, _headMemos, _headBound, _prepared,
      _nonterminal, _post, captured, _completed⟩ := ordinary
    have fields := SourcePruningEnumerationCapturedEdge.observed_cache_ancestry_extension captured
    exact enteredExtends.trans fields.1
  · obtain ⟨_gate, running, _post, _captured, _completed, _admitted, _pending, _history⟩ := otherBranch
    have fields := SourcePruningEnumerationSelectedOpaqueDispatch.observed_cache_ancestry_extension running
    exact enteredExtends.trans fields.1

/-- The actual recording callback retains every original per-slot recursion key. -/
theorem SelectedHistoryReceipt.ancestry_extension_after_callback
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) : Extends before.core callbackCore := by
  have completed := receipt.ancestry_extension
  have packet := receipt.completed_packet
  have frame := SourcePruningRecordTypes.recordTypes_frame graph templates callbackFuel metadata uv (.inl fragment)
    after.core callbackCore result packet.safe.1.total recorded
  exact completed.trans (Extends.frame frame)

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
