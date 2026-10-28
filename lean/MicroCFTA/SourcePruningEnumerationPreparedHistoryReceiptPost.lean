import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryContract

/-!
# Native Post through one actual prepared selected receipt

The preparation retains its original full memo state.
Each completed branch retains its actual reached caller and returned Memos.
The actual native Posts compose in execution order.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable [DecidableEq Node]

/-- The actual preparation and either completed branch retain the exact full endpoint Post. -/
theorem SelectedHistoryReceipt.native_post
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
    {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
    {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos) :
    Post formulas solver returnedInventory caller reached returnedMemos := by
  obtain ⟨_entered, _handle, _scs, _decoded, _prepared, _heap, _preparationBound,
    _original, _ready, _stored, _preparing, _actual, _lookup, preparationPost,
    _enteredPacket, _stable, _enteredReady, _enteredStored, _counter, _values,
    _flags, _waiting, _available, _closed, _language, branches⟩ := receipt
  rcases branches with ordinary | otherBranch
  · obtain ⟨_parentEntry, _edges, _depth, _free, _edge, _headSeed, _inherited,
      _headInventory, _headCaller, _headMemos, _headBound, _prepared,
      _nonterminal, headPost, _captured, completed⟩ := ordinary
    exact (preparationPost.trans headPost).trans completed.post
  · obtain ⟨_gate, _running, post, _captured, _completed, _admitted, _pending, _history⟩ := otherBranch
    exact preparationPost.trans post

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
