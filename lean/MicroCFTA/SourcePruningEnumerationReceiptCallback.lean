import MicroCFTA.SourcePruningEnumerationNativeCacheFrame
import MicroCFTA.SourcePruningCallbackCompletion

namespace MicroCFTA.SourcePruningEnumerationReceiptCallback
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationOrder EnumerationCompressionFrame
open SourcePruningEnumerationNativeBranchCompletion SourcePruningRecordTypes SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
variable {Typing : Type} {width : Nat}

/-- A completed receipt runs the concrete fragment callback at its own cache. -/
def Completes (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (before : EnumerationState.State Symbol Constraint) :
    Receipt width → Prop
  | .complete fragment caller queries after =>
      ∀ level frontier, Stratified before level frontier →
        (∀ group ∈ metadata.pending, PendingBound before.counter group) →
        ∃ nextLevel fuel result final,
          Success (recordTypes graph templates fuel metadata uv (.inl fragment)) after.core result final ∧
          RenderStable after.core final ∧ Frame after.core final ∧ Stratified final nextLevel (frontier + 1) ∧
          result.2.types = updatedTypes metadata uv (.inl fragment) ∧
          result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
          Admitted uv (.complete fragment caller queries (EnumerationExpandableIndex.frame final after)) ∧
          FragmentHistory before (.complete fragment caller queries (EnumerationExpandableIndex.frame final after)) ∧
          (Pending (.complete fragment caller queries after) →
            Pending (.complete fragment caller queries (EnumerationExpandableIndex.frame final after))) ∧
          (∀ preference, EnumerationPureSelection.next preference (EnumerationExpandableIndex.frame final after) =
            EnumerationPureSelection.next preference after) ∧
          ∀ group ∈ result.2.pending, PendingBound final.counter group
  | _ => True

/-- Actual receipt invariants derive callback completion from original bounds and dependency levels. -/
theorem completes (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (before : EnumerationState.State Symbol Constraint)
    (receipt : Receipt width) (admitted : Admitted uv receipt) (history : FragmentHistory before receipt) :
    Completes graph templates metadata uv before receipt := by
  cases receipt with
  | complete fragment caller queries after =>
      intro level frontier ordered bounded
      obtain ⟨nextLevel, afterOrder⟩ := history.2.2 level frontier ordered
      have afterBounded : ∀ group ∈ metadata.pending, PendingBound after.core.counter group := by
        intro group member entry listed
        exact Nat.lt_of_lt_of_le (bounded group member entry listed) history.1
      obtain ⟨fuel, result, final, success, stable, frame, finalOrder, types, holes, typing, finalBounded⟩ :=
        recordTypes_inl_complete_bounded graph templates nextLevel (frontier + 1) metadata uv fragment
          after.core admitted.2.1 afterOrder admitted.2.2.1 afterBounded
      exact ⟨nextLevel, fuel, result, final, success, stable, frame, finalOrder, types, holes, typing,
        admitted_complete_frame uv fragment caller queries after final frame stable.safe admitted,
        fragmentHistory_complete_frame before fragment caller queries after final frame history,
        fun pending => pending_complete_frame fragment caller queries after final frame pending,
        fun preference => selection_frame preference after final frame.counter,
        finalBounded⟩
  | unhandled | rejected _ _ _ | stopped _ _ _ => trivial

end MicroCFTA.SourcePruningEnumerationReceiptCallback
