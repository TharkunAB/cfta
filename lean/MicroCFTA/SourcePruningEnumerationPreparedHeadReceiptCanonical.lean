import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission
import MicroCFTA.SourcePruningEnumerationPreparedCapturedCanonical

/-!
# Canonical storage through an actual prepared completed head

The prepared parent supplies its own native availability and closure proofs.
The original stored bucket supplies inherited trie validity.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual prepared completed head preserves canonical stored suspended tries. -/
theorem CompletedHeadReceipt.canonical
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
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
    (canonical : Canonical before.core) : Canonical after.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := receipt.projected
  have pending := EnumerationReferences.pending_inputs before.core receipt.admission.packet.pending
    uv (some handle) scs receipt.admission.stored
  exact SourcePruningEnumerationCapturedEdge.complete_canonical_prepared formulas solver inventory
    caller before checkEmpty uv handle scs parentEntry storedEdges depth free edge roots memos
    receipt.admission.packet.context receipt.admission.ready receipt.admission.stored
    receipt.admission.parentAvailable receipt.admission.parentClosed realized receipt.admission.selected
    paths counts flags pending receipt.allowed tries residual projected canonical
    (by simpa only [Nat.add_zero] using receipt.running 0)

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
