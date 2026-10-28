import MicroCFTA.SourcePruningEnumerationPreparedHistoryReceiptCanonical
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationPreparedCapturedIsolation
import MicroCFTA.SourcePruningEnumerationPreparedOpaqueReceiptIsolation
import MicroCFTA.SourcePruningEnumerationIsolationReads

/-!
# Original isolation through the same actual prepared selected receipt

The preparation retains the original enumeration cache.
The ordinary and opaque receipts retain a different isolated root.
The same native Post receipts retain the original handle readback.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDischargeHistory InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
variable {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
variable {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
variable {returnedInventory : Inventory} {returnedMemos : Memos} {held heldHandle : Nat}

/-- Both actual selected receipt arms retain the original different isolated slot and complete native Post. -/
theorem SelectedHistoryReceipt.isolated_post
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (isolated : IsolatedPending held heldHandle before.core) (different : held ≠ uv) :
    IsolatedPending held heldHandle after.core ∧
      Post formulas solver returnedInventory caller reached returnedMemos := by
  obtain ⟨entered, handle, scs, decoded, prepared, heap, preparationBound,
    original, ready, stored, preparing, atWork, decodedLookup, preparationPost,
    enteredPacket, stable, enteredReady, enteredStored, counter, values, flags, waiting,
    available, closed, exactMeaning, branch⟩ := receipt
  have enteredIsolated := isolated.through_renderStable stable
  rcases branch with ordinary | otherBranch
  · obtain ⟨parentEntry, edges, depth, free, edge, headSeed, inherited, headInventory,
      headCaller, headMemos, headBound, same, nonterminal, prefixPost, observed, completed⟩ := ordinary
    exact ⟨completed.isolated enteredIsolated different,
      preparationPost.trans (prefixPost.trans completed.post)⟩
  · obtain ⟨dispatch, observed, headPost, captured, completed, admitted, pending, history⟩ := otherBranch
    have bounded : ∀ sc ∈ scs, sc.var < entered.core.counter :=
      enteredPacket.safe.1.values _ (List.mem_of_getElem? enteredStored)
    have inputs : Avoids entered.core.representatives held scs :=
      enteredIsolated.incoming _ (List.mem_of_getElem? enteredStored)
    have retained := SourcePruningEnumerationSelectedOpaqueDispatch.completed_isolated
      checkEmpty workFuel workFuel workFuel workFuel workFuel uv scs prepared
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) reached entered after
      memos.query returnedMemos.query fragment held heldHandle enteredPacket.safe enteredIsolated
      (Ne.symm different) bounded inputs observed
    exact ⟨retained, preparationPost.trans headPost⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
