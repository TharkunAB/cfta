import MicroCFTA.SourcePruningEnumerationPathReceiptsRaw
import MicroCFTA.SourcePruningEnumerationPathPreparedOpaqueRaw
import MicroCFTA.SourcePruningEnumerationPreparedRecursive

/-!
# Paths in retained recursive execution data

The predicates inspect every output and retained stop field.
Fold paths include processed receipts before finish discards them.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionPathData
open SourcePruningEnumerationPathTransport (StatePaths)
open SourcePruningEnumerationPathSelectedRaw (RawPaths SelectedPrefixPaths)
open SourcePruningEnumerationPathObservationRaw (ObservationPaths)
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Output" => SourcePruningEnumerationRecursive.Output
local notation "NativeFailure" => SourcePruningEnumerationRecursive.Failure
local notation "PreparedFailure" => SourcePruningEnumerationPreparedRecursive.Failure
local notation "Stop" => SourcePruningEnumerationNativeContinuations.Stop
local notation "Fold" => SourcePruningEnumerationNativeContinuations.Result
local notation "Hook" => SourcePruningEnumerationNativeContinuations.HookResult
universe v
variable {width : Nat} {Typing : Type} {Reason : Type v}

/-- A receipt retains its cache paths and every successful raw observation row. -/
def FullReceiptPaths (P : EqualityTrie.Path → Prop) (receipt : Receipt width) : Prop :=
  SourcePruningEnumerationPathPreparedOpaque.ReceiptPaths P receipt ∧
    match receipt with
    | .stopped _ observation _ => ObservationPaths P observation
    | _ => True

/-- Every emitted output retains paths in its own cache. -/
def OutputsPaths (P : EqualityTrie.Path → Prop) (outputs : List (Output width Typing)) : Prop :=
  ∀ output ∈ outputs, StatePaths P output.cache.core

/-- Every cache and raw row retained in a native failure has the supplied paths. -/
def NativeFailurePaths (P : EqualityTrie.Path → Prop) : NativeFailure width Typing → Prop
  | .exhausted _ _ before => StatePaths P before.core
  | .selected _ observed => SelectedPrefixPaths P observed
  | .callback _ raw => RawPaths P raw
  | .ordinary _ raw => RawPaths P raw
  | .alternatives _ processed current =>
      (∀ receipt ∈ processed, FullReceiptPaths P receipt) ∧
        match current with
        | .edge optional => ∀ receipt, optional = some receipt → FullReceiptPaths P receipt
        | .continuation receipt reason _ => FullReceiptPaths P receipt ∧ NativeFailurePaths P reason

/-- Every cache and raw row retained in a prepared failure has the supplied paths. -/
def PreparedFailurePaths (P : EqualityTrie.Path → Prop) : PreparedFailure width Typing → Prop
  | .exhausted _ _ before => StatePaths P before.core
  | .selected _ observed => SelectedPrefixPaths P observed
  | .callback _ raw => RawPaths P raw
  | .preparation _ observation => RawPaths P observation.1
  | .alternatives _ processed current =>
      (∀ receipt ∈ processed, FullReceiptPaths P receipt) ∧
        match current with
        | .edge optional => ∀ receipt, optional = some receipt → FullReceiptPaths P receipt
        | .continuation receipt reason _ => FullReceiptPaths P receipt ∧ PreparedFailurePaths P reason

/-- The current stop retains its receipt and the paths required by its actual reason. -/
def StopPaths (P : EqualityTrie.Path → Prop) (reasonPaths : Reason → Prop) : Stop Reason width → Prop
  | .edge optional => ∀ receipt, optional = some receipt → FullReceiptPaths P receipt
  | .continuation receipt reason _ => FullReceiptPaths P receipt ∧ reasonPaths reason

/-- The actual fold retains processed receipts even when its output list is empty. -/
def FoldPaths (P : EqualityTrie.Path → Prop) (reasonPaths : Reason → Prop) :
    Fold (Output width Typing) Reason width → Prop
  | .complete processed outputs _ _ =>
      (∀ receipt ∈ processed, FullReceiptPaths P receipt) ∧ OutputsPaths P outputs
  | .stopped processed outputs current =>
      (∀ receipt ∈ processed, FullReceiptPaths P receipt) ∧ OutputsPaths P outputs ∧
        StopPaths P reasonPaths current

/-- An actual outcome retains every output cache and its complete stored failure data. -/
def OutcomePaths (P : EqualityTrie.Path → Prop) (reasonPaths : Reason → Prop) :
    Hook (Output width Typing) Reason width → Prop
  | .complete outputs _ _ => OutputsPaths P outputs
  | .stopped outputs reason _ => OutputsPaths P outputs ∧ reasonPaths reason

/-- Native finish retains output and failure paths from its actual complete fold data. -/
theorem native_finish_paths {P : EqualityTrie.Path → Prop} (uv : Nat)
    (folded : Fold (Output width Typing) (NativeFailure width Typing) width)
    (paths : FoldPaths P (NativeFailurePaths P) folded) :
    OutcomePaths P (NativeFailurePaths P) (SourcePruningEnumerationRecursive.finish uv folded) := by
  cases folded with
  | complete processed outputs caller queries => exact paths.2
  | stopped processed outputs current =>
      obtain ⟨processedPaths, outputPaths, stopPaths⟩ := paths
      cases current <;> exact ⟨outputPaths, processedPaths, stopPaths⟩

/-- Prepared finish retains output and failure paths from its actual complete fold data. -/
theorem prepared_finish_paths {P : EqualityTrie.Path → Prop} (uv : Nat)
    (folded : Fold (Output width Typing) (PreparedFailure width Typing) width)
    (paths : FoldPaths P (PreparedFailurePaths P) folded) :
    OutcomePaths P (PreparedFailurePaths P) (SourcePruningEnumerationPreparedRecursive.finish uv folded) := by
  cases folded with
  | complete processed outputs caller queries => exact paths.2
  | stopped processed outputs current =>
      obtain ⟨processedPaths, outputPaths, stopPaths⟩ := paths
      cases current <;> exact ⟨outputPaths, processedPaths, stopPaths⟩

end MicroCFTA.SourcePruningEnumerationExecutionPathData
