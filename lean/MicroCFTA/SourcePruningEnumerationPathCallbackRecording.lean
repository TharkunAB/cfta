import MicroCFTA.SourcePruningEnumerationPathHead
import MicroCFTA.SourcePruningRecordTypes

/-!
# Actual callback recording preserves original forecast paths

The result concerns the recorded state before the recursive continuation.
-/

namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]


/-- Every actual successful recording keeps the original forecast path predicate. -/
theorem CompletedHeadReceipt.recorded_paths_of_forecast
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {storedEdges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv handle scs parentEntry storedEdges depth free edge bound fragment reached saved after
      returnedInventory returnedMemos)
    (guards : List Constraint) (P : EqualityTrie.Path → Prop)
    (included : seed.1 ⊆ guards) (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (original : StatePaths P before.core)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (work : Nat) (recorded : Bool × SourcePruningRecordTypes.Metadata Typing)
    (callbackCore : EnumerationState.State Symbol Constraint)
    (observed : Success
      (SourcePruningRecordTypes.recordTypes graph templates work metadata uv (.inl fragment))
      after.core recorded callbackCore) :
    StatePaths P (EnumerationExpandableIndex.frame callbackCore after).core := by
  have headPaths := receipt.paths_of_forecast guards P included projected tails original
  have framed := SourcePruningRecordTypes.recordTypes_frame graph templates work metadata uv
    (.inl fragment) after.core callbackCore recorded receipt.completed.safe.1.total observed
  change StatePaths P callbackCore
  exact SourcePruningEnumerationPathStorage.values_paths headPaths framed.values

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources

namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationCorrectness InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]


/-- Every actual successful recording keeps the original forecast path predicate. -/
theorem CompletedHeadReceipt.recorded_paths_of_forecast
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    (guards : List Constraint) (P : EqualityTrie.Path → Prop)
    (included : seed.1 ⊆ guards) (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (original : StatePaths P before.core)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (work : Nat) (recorded : Bool × SourcePruningRecordTypes.Metadata Typing)
    (callbackCore : EnumerationState.State Symbol Constraint)
    (observed : Success
      (SourcePruningRecordTypes.recordTypes graph templates work metadata uv (.inl fragment))
      after.core recorded callbackCore) :
    StatePaths P (EnumerationExpandableIndex.frame callbackCore after).core := by
  have headPaths := receipt.paths_of_forecast guards P included projected tails original
  have framed := SourcePruningRecordTypes.recordTypes_frame graph templates work metadata uv
    (.inl fragment) after.core callbackCore recorded receipt.completed.safe.1.total observed
  change StatePaths P callbackCore
  exact SourcePruningEnumerationPathStorage.values_paths headPaths framed.values

end MicroCFTA.SourcePruningEnumerationNativeHookResources
