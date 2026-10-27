import MicroCFTA.SourceFlatPruningContinuation
import MicroCFTA.SourceFlatPruningNativeContinuations
import MicroCFTA.SourcePruningEnumerationRecursive
import MicroCFTA.SourcePruningCallbackExact

/-!
# Correspondence of concrete callback continuations

Successful original callbacks supply their actual flat rows by replay.
The recursive hypothesis applies only at the returned callback cache.
The structural helper passes every unexpected raw list to its diagnostic constructor.
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
local notation "Raw" => List (Except Error ((Bool × Metadata Typing) × Core))

private theorem raw_related
    (outputsRelated : Out → OldOutput → Prop) (reasonsRelated : Reason → OldReason → Prop)
    (callbackFailure : Nat → FlatRaw → Reason)
    (recur : Metadata Typing → Caller width → Queries → FlatCached → Option Next → Hook)
    (oldRecur : Metadata Typing → Caller width → Queries → Cached → Option Next → OldHook)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (uv : Nat) (caller : Caller width) (queries : Queries) (flat : FlatCached) (before : Cached)
    (related : EnumerationFlatCached.Related flat before)
    (flatRaw : FlatRaw) (earlierRaw : Raw)
    (rows : EnumerationResultRelation.Results EnumerationFlatState.Related flatRaw earlierRaw)
    (recursive : ∀ updated nextFlat nextOld,
      flatRaw = [.ok ((false, updated), nextFlat)] →
      earlierRaw = [.ok ((false, updated), nextOld)] →
      EnumerationFlatCached.Related (EnumerationFlatCached.frame nextFlat flat)
        (EnumerationExpandableIndex.frame nextOld before) →
      SourceFlatPruningNativeContinuations.HookResultRelated outputsRelated reasonsRelated
        (recur updated caller queries (EnumerationFlatCached.frame nextFlat flat)
          (SourcePruningEnumerationRestart.decision stop order updated
            (EnumerationExpandableIndex.frame nextOld before)))
        (oldRecur updated caller queries (EnumerationExpandableIndex.frame nextOld before)
          (SourcePruningEnumerationRestart.decision stop order updated
            (EnumerationExpandableIndex.frame nextOld before))))
    (diagnostic : reasonsRelated (callbackFailure uv flatRaw)
      (SourcePruningEnumerationRecursive.Failure.callback uv earlierRaw)) :
    SourceFlatPruningNativeContinuations.HookResultRelated outputsRelated reasonsRelated
      (match flatRaw with
      | [.ok ((true, _updated), _observed)] => .complete [] caller queries
      | [.ok ((false, updated), observed)] =>
          recur updated caller queries (EnumerationFlatCached.frame observed flat)
            (SourceFlatPruningRestart.decision stop order updated (EnumerationFlatCached.frame observed flat))
      | _ => .stopped [] (callbackFailure uv flatRaw) (some (caller, queries)))
      (match earlierRaw with
      | [.ok ((true, _updated), _observed)] => .complete [] caller queries
      | [.ok ((false, updated), observed)] =>
          oldRecur updated caller queries (EnumerationExpandableIndex.frame observed before)
            (SourcePruningEnumerationRestart.decision stop order updated
              (EnumerationExpandableIndex.frame observed before))
      | _ => .stopped [] (SourcePruningEnumerationRecursive.Failure.callback uv earlierRaw)
          (some (caller, queries))) := by
  cases rows with
  | nil => exact ⟨.nil, diagnostic, rfl⟩
  | cons head tail =>
      cases tail with
      | nil =>
          cases head with
          | error error => exact ⟨.nil, diagnostic, rfl⟩
          | ok result cores =>
              obtain ⟨pruned, updated⟩ := result
              cases pruned with
              | true => exact ⟨.nil, rfl, rfl⟩
              | false =>
                  have caches := EnumerationFlatCached.frame_related related cores
                  rw [SourceFlatPruningRestart.decision_related caches stop order updated]
                  exact recursive updated _ _ rfl rfl caches
      | cons next rest =>
          cases head with
          | error error => exact ⟨.nil, diagnostic, rfl⟩
          | ok result cores =>
              obtain ⟨pruned, updated⟩ := result
              cases pruned <;> exact ⟨.nil, diagnostic, rfl⟩

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
            (EnumerationExpandableIndex.frame after before))))
    (diagnostics : ∀ flatRaw earlierRaw,
      EnumerationResultRelation.Results EnumerationFlatState.Related flatRaw earlierRaw →
      reasonsRelated (callbackFailure uv flatRaw)
        (SourcePruningEnumerationRecursive.Failure.callback uv earlierRaw)) :
    SourceFlatPruningNativeContinuations.HookResultRelated outputsRelated reasonsRelated
      (SourceFlatPruningContinuation.continueWith callbackFailure recur graph templates stop order
        callbackFuel metadata uv fragment caller queries flat)
      (SourcePruningEnumerationRecursive.continueWith oldRecur graph templates stop order
        callbackFuel metadata uv fragment caller queries before) := by
  obtain ⟨nextFlat, flatExact, cores⟩ := SourceFlatPruningOracle.recordTypes_replays graph templates
    callbackFuel metadata uv (.inl fragment) flat.core before.core result after related.core success
  have oldExact := SourcePruningCallbackExact.recordTypes_exact graph templates callbackFuel metadata uv
    (.inl fragment) before.core after result success
  have rows : EnumerationResultRelation.Results EnumerationFlatState.Related
      (SourceFlatPruningOracle.recordTypes graph templates callbackFuel metadata uv (.inl fragment) flat.core)
      (ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
        (.inl fragment) before.core)) := by
    rw [flatExact, oldExact]
    exact .cons (.ok result cores) .nil
  unfold SourceFlatPruningContinuation.continueWith SourcePruningEnumerationRecursive.continueWith
  apply raw_related outputsRelated reasonsRelated callbackFailure recur oldRecur stop order uv caller queries
    flat before related _ _ rows
  · intro updated observedFlat observedOld _flatSingle oldSingle caches
    have same : (result, after) = ((false, updated), observedOld) :=
      Except.ok.inj (List.cons.inj (oldExact.symm.trans oldSingle)).1
    obtain ⟨resultSame, afterSame⟩ := Prod.mk.inj same
    subst result observedOld
    exact recursive rfl observedFlat caches
  · exact diagnostics _ _ rows

end MicroCFTA.SourceFlatPruningContinuationCorrespondence
