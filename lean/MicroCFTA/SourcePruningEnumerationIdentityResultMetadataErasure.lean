import MicroCFTA.SourcePruningEnumerationIdentityPrefixMetadataErasure
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

set_option autoImplicit false

/-!
# Exact metadata projections for the existing prepared worker

The projections retain all fields except metadata.
The transport statements retain both complete and stopped results.
These projections support erasure through the existing worker.
-/
namespace MicroCFTA.SourcePruningEnumerationIdentityResultMetadataErasure
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish continueWith)
open SourcePruningEnumerationIdentityPrefixMetadataErasure (eraseMetadata erasePrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Hook" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "Stop" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Stop
local notation "Fold" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
variable {width : Nat}

/-- Erase optional metadata and retain the output's cache and native endpoint. -/
def eraseOutput {Typing : Type} (output : Output width Typing) : Output width Unit :=
  ⟨output.metadata.map eraseMetadata, output.cache, output.caller, output.queries⟩

/-- Erase metadata in the existing failure and retain every receipt and endpoint. -/
def eraseFailure {Typing : Type} : Failure width Typing → Failure width Unit
  | .exhausted uv metadata before => .exhausted uv (eraseMetadata metadata) before
  | .selected uv observed => .selected uv (erasePrefix observed)
  | .callback uv raw => .callback uv (raw.map fun
      | .error fault => .error fault
      | .ok ((flag, metadata), after) => .ok ((flag, eraseMetadata metadata), after))
  | .preparation uv raw => .preparation uv raw
  | .alternatives uv processed (.edge current reached) =>
      .alternatives uv processed (.edge current reached)
  | .alternatives uv processed (.continuation current reason reached) =>
      .alternatives uv processed (.continuation current (eraseFailure reason) reached)

/-- Retain the complete or stopped constructor and every native endpoint. -/
def eraseResult {Typing : Type} :
    Hook (Output width Typing) (Failure width Typing) width →
      Hook (Output width Unit) (Failure width Unit) width
  | .complete outputs caller queries => .complete (outputs.map eraseOutput) caller queries
  | .stopped outputs reason reached => .stopped (outputs.map eraseOutput) (eraseFailure reason) reached

/-- Erase a continuation reason and retain the edge receipt and endpoint. -/
def eraseStop {Typing : Type} : Stop (Failure width Typing) width → Stop (Failure width Unit) width
  | .edge current reached => .edge current reached
  | .continuation current reason reached => .continuation current (eraseFailure reason) reached

/-- Retain processed receipts, output order, stop context, and native endpoints. -/
def eraseFold {Typing : Type} :
    Fold (Output width Typing) (Failure width Typing) width →
      Fold (Output width Unit) (Failure width Unit) width
  | .complete processed outputs caller queries =>
      .complete processed (outputs.map eraseOutput) caller queries
  | .stopped processed outputs current =>
      .stopped processed (outputs.map eraseOutput) (eraseStop current)

/-- Alternative failures use the same stop projection as the enclosing fold. -/
theorem eraseFailure_alternatives {Typing : Type} (uv : Nat) (processed : List (Receipt width))
    (current : Stop (Failure width Typing) width) :
    eraseFailure (.alternatives uv processed current) =
      .alternatives uv processed (eraseStop current) := by
  cases current <;> rfl

/-- Finishing the actual fold commutes with metadata erasure. -/
theorem finish_erasure {Typing : Type} (uv : Nat)
    (folded : Fold (Output width Typing) (Failure width Typing) width) :
    eraseResult (finish uv folded) = finish uv (eraseFold folded) := by
  cases folded with
  | complete processed outputs caller queries => rfl
  | stopped processed outputs current => cases current <;> rfl

/-- Erasure commutes with the actual scan, including every stopped suffix. -/
theorem scan_erasure {Typing : Type}
    (visit : Edge → Caller width → Queries → Cached →
      Fold (Output width Typing) (Failure width Typing) width)
    (before : Cached) (edges : List Edge) (caller : Caller width) (queries : Queries) :
    eraseFold (SourcePruningEnumerationSharedBranching.scan visit before edges caller queries) =
      SourcePruningEnumerationSharedBranching.scan
        (fun edge reached saved cache => eraseFold (visit edge reached saved cache))
        before edges caller queries := by
  induction edges generalizing caller queries with
  | nil => rfl
  | cons edge rest ih =>
      cases observed : visit edge caller queries before with
      | stopped processed outputs current =>
          simp only [SourcePruningEnumerationSharedBranching.scan, observed, eraseFold]
      | complete processed outputs reached saved =>
          have erasedHead : eraseFold (.complete processed outputs reached saved) =
              .complete processed (outputs.map eraseOutput) reached saved := rfl
          simp only [SourcePruningEnumerationSharedBranching.scan, observed, erasedHead]
          rw [← ih reached saved]
          cases SourcePruningEnumerationSharedBranching.scan visit before rest reached saved <;>
            simp only [eraseFold, List.map_append]

/-- The actual single-receipt continuation commutes with erasure. -/
theorem receipt_erasure {Typing : Type}
    (hook : Fragment → Caller width → Queries → Cached →
      Hook (Output width Typing) (Failure width Typing) width)
    (caller : Caller width) (queries : Queries) (receipt : Option (Receipt width)) :
    eraseFold (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries receipt) =
      SourcePruningEnumerationSharedReceiptContinuation.run
        (fun fragment reached saved after => eraseResult (hook fragment reached saved after))
        caller queries receipt := by
  cases receipt with
  | none => rfl
  | some receipt =>
      cases receipt with
      | complete fragment reached saved after =>
          simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
          cases hook fragment reached saved after <;> rfl
      | unhandled => rfl
      | rejected reached saved after => rfl
      | finalizeStopped fragment reached saved after => rfl
      | stopped fragments observation candidate =>
          simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
          cases SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
            (.stopped fragments observation candidate) with
          | none => rfl
          | some endpoint => cases endpoint; rfl

/-- An empty catalog supplies the same Core before the actual recursive call. -/
theorem continue_empty_exact {Typing : Type}
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next →
      Hook (Output width Typing) (Failure width Typing) width)
    (graph : Graph Symbol Constraint) (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (fragment : Fragment) (caller : Caller width) (queries : Queries) (before : Cached) :
    continueWith recur graph [] none (fun _ _ => none) callbackFuel metadata uv
      fragment caller queries before =
    recur {metadata with types := SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment)}
      caller queries (EnumerationExpandableIndex.frame before.core before)
      (some (EnumerationPureSelection.next (fun _ => none)
        (EnumerationExpandableIndex.frame before.core before))) := by
  unfold continueWith
  rw [SourcePruningRecordTypes.recordTypes_empty]
  rfl

end MicroCFTA.SourcePruningEnumerationIdentityResultMetadataErasure
