import MicroCFTA.SourcePruningEnumerationTraversalAncestryExtension
import MicroCFTA.SourcePruningEnumerationAncestryExtensionOwn
import MicroCFTA.SourcePruningEnumerationCapturedEdge
import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission

/-!
# Actual prepared head history extension

Own classes and each actual child retain every per-slot history key.
Residual recording keeps the active expansion history.
Captured finalization keeps all slot keys and clears expansion ancestry.
The actual prepared head receipt supplies that same captured completion.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual selected-head cache extends its own input and keeps expansion ancestry. -/
theorem observed_cache_ancestry_extension
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {caller : Caller width} {before : Cached} {queries : Queries}
    {result : Result width}
    (observed : run checkEmpty r n p h k scs edge caller before queries = result) :
    match (generalizing := false) result with
    | .complete _ _ _ after | .rejected _ _ after =>
        Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry
    | .stopped _ _ (some after) =>
        Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry
    | _ => True := by
  rw [← observed]
  unfold run
  cases own : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => trivial
  | some rows =>
      cases rows with
      | nil => exact ⟨Extends.refl _, rfl⟩
      | cons row rest =>
          obtain ⟨⟨symbol, staged, residual⟩, middle⟩ := row
          cases rest with
          | cons next later => trivial
          | nil =>
              have ownFields := SourcePruningEnumerationCachedOwn.prepare_ancestry_extension own _
                (List.mem_singleton_self _)
              dsimp only
              cases children : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | stopped fragments observation candidate =>
                  cases candidate with
                  | none => trivial
                  | some after =>
                      have childFields :=
                        SourcePruningEnumerationChildTraversal.stopped_ancestry_extension children
                      exact ⟨ownFields.1.trans childFields.1, childFields.2.trans ownFields.2⟩
              | complete fragments reached saved after =>
                  have childFields := SourcePruningEnumerationChildTraversal.complete_ancestry_extension children
                  have finishFields := finish_ancestry_extension residual (.node symbol fragments) after
                  exact ⟨ownFields.1.trans (childFields.1.trans finishFields.1),
                    finishFields.2.trans (childFields.2.trans ownFields.2)⟩

end MicroCFTA.SourcePruningEnumerationSelectedEdge

namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual captured finalization extends every slot and clears only the active history. -/
theorem observed_cache_ancestry_extension
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {caller : Caller width} {before : Cached} {queries : Queries}
    {result : Result width}
    (observed : run checkEmpty r n p h k target scs edge caller before queries = some result) :
    match (generalizing := false) result with
    | .complete _ _ _ after => Extends before.core after.core ∧ after.core.expansionAncestry = []
    | .rejected _ _ after | .stopped _ _ (some after) =>
        Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry
    | _ => True := by
  unfold run at observed
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | unhandled | rejected =>
      simp only [selected] at observed
      cases observed
      exact SourcePruningEnumerationSelectedEdge.observed_cache_ancestry_extension selected
  | stopped completedPrefix observation candidate =>
      simp only [selected] at observed
      cases observed
      cases candidate with
      | none => trivial
      | some after =>
          exact SourcePruningEnumerationSelectedEdge.observed_cache_ancestry_extension selected
  | complete fragment reached saved middle =>
      simp only [selected] at observed
      obtain ⟨finished, finalized, same⟩ := Option.map_eq_some_iff.mp observed
      have middleFields := SourcePruningEnumerationSelectedEdge.observed_cache_ancestry_extension selected
      have finishedFields := SourcePruningEnumerationFinalize.run_ancestry_extension
        reached.checked.native.machine.heap k target fragment middle finished finalized
      cases same
      exact ⟨middleFields.1.trans finishedFields.1, finishedFields.2⟩

end MicroCFTA.SourcePruningEnumerationCapturedEdge

namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- The actual prepared completed head extends all slot histories from its own captured input. -/
theorem CompletedHeadReceipt.ancestry_extension
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller reached : Caller (bits + 2)} {memos returnedMemos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before after : Cached}
    {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {saved : SourceEndpointMemo.Memos}
    {returnedInventory : Inventory}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata
      before checkEmpty uv handle scs parentEntry edges depth free edge bound fragment reached
      saved after returnedInventory returnedMemos) :
    Extends before.core after.core ∧ after.core.expansionAncestry = [] := by
  have actual := receipt.running 0
  simp only [Nat.add_zero] at actual
  exact SourcePruningEnumerationCapturedEdge.observed_cache_ancestry_extension actual

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
