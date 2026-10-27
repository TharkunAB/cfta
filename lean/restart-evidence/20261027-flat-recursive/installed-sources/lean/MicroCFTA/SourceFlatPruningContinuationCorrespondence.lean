import MicroCFTA.SourceFlatPruningContinuation
import MicroCFTA.SourceFlatPruningNativeContinuations
import MicroCFTA.SourcePruningEnumerationRecursive
import MicroCFTA.SourcePruningCallbackExact

/-!
# Correspondence of concrete callback continuations

Successful original callbacks supply their actual flat rows by replay.
The recursive hypothesis applies only at the returned callback cache.
The callback singleton excludes the diagnostic branch at this observed execution.
-/

namespace MicroCFTA.SourceFlatPruningContinuationCorrespondence
open EnumerationState SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "FlatCore" => EnumerationFlatState.State Symbol Constraint
universe u v
variable {Typing : Type} {width : Nat} {Out : Type u} {Reason : Type v}
local notation "OldOutput" => SourcePruningEnumerationRecursive.Output width Typing
local notation "OldReason" => SourcePruningEnumerationRecursive.Failure width Typing
local notation "Hook" => SourcePruningEnumerationNativeContinuations.HookResult Out Reason width
local notation "OldHook" => SourcePruningEnumerationNativeContinuations.HookResult OldOutput OldReason width
local notation "FlatRaw" => List (Except Error ((Bool × Metadata Typing) × FlatCore))

/-- Replay an actual successful callback before applying the recursive hypothesis at its own cache. -/
theorem continueWith_success
    (outputsRelated : Out → OldOutput → Prop) (reasonsRelated : Reason → OldReason → Prop)
    (callbackFailure : Nat → FlatRaw → Reason)
    (recur : Metadata Typing → Caller width → Queries → FlatCached → Option Next → Hook)
    (oldRecur : Metadata Typing → Caller width → Queries → Cached → Option Next → OldHook)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (flat : FlatCached) (before : Cached)
    (related : EnumerationFlatCached.Related flat before)
    (result : Bool × Metadata Typing) (after : Core)
    (success : EnumerationCorrectness.Success (SourcePruningRecordTypes.recordTypes
      graph templates callbackFuel metadata uv (.inl fragment)) before.core result after)
    (recursive : result.1 = false → ∀ nextFlat,
      EnumerationFlatCached.Related (EnumerationFlatCached.frame nextFlat flat)
        (EnumerationExpandableIndex.frame after before) →
      SourceFlatPruningNativeContinuations.HookResultRelated outputsRelated reasonsRelated
        (recur result.2 caller queries (EnumerationFlatCached.frame nextFlat flat)
          (SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before)))
        (oldRecur result.2 caller queries (EnumerationExpandableIndex.frame after before)
          (SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before)))) :
    SourceFlatPruningNativeContinuations.HookResultRelated outputsRelated reasonsRelated
      (SourceFlatPruningContinuation.continueWith callbackFailure recur graph templates stop order
        callbackFuel metadata uv fragment caller queries flat)
      (SourcePruningEnumerationRecursive.continueWith oldRecur graph templates stop order
        callbackFuel metadata uv fragment caller queries before) := by
  obtain ⟨nextFlat, flatExact, cores⟩ := SourceFlatPruningOracle.recordTypes_replays graph templates
    callbackFuel metadata uv (.inl fragment) flat.core before.core result after related.core success
  have oldExact := SourcePruningCallbackExact.recordTypes_exact graph templates callbackFuel metadata uv
    (.inl fragment) before.core after result success
  unfold SourceFlatPruningContinuation.continueWith SourcePruningEnumerationRecursive.continueWith
  rw [flatExact, oldExact]
  obtain ⟨pruned, updated⟩ := result
  cases pruned with
  | true => exact ⟨.nil, rfl, rfl⟩
  | false =>
      have caches := EnumerationFlatCached.frame_related related cores
      change SourceFlatPruningNativeContinuations.HookResultRelated outputsRelated reasonsRelated
        (recur updated caller queries (EnumerationFlatCached.frame nextFlat flat)
          (SourceFlatPruningRestart.decision stop order updated (EnumerationFlatCached.frame nextFlat flat)))
        (oldRecur updated caller queries (EnumerationExpandableIndex.frame after before)
          (SourcePruningEnumerationRestart.decision stop order updated
            (EnumerationExpandableIndex.frame after before)))
      rw [SourceFlatPruningRestart.decision_related caches stop order updated]
      exact recursive rfl nextFlat caches

end MicroCFTA.SourceFlatPruningContinuationCorrespondence
