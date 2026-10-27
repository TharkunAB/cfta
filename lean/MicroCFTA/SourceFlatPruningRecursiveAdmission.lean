import MicroCFTA.SourceFlatPruningContinuation
import MicroCFTA.SourcePruningEnumerationRecursiveCallback
import MicroCFTA.SourcePruningEnumerationSubtreeEffects
import MicroCFTA.SourcePruningEnumerationSuspendedMass
import MicroCFTA.EnumerationFlatNativeIndex

/-!
# Original admission at actual flat callback and sibling endpoints

The callback producer supplies its original packet once. Successful replay
uses that same callback receipt. A completed subtree supplies the actual
native caller and full memos for the captured sibling cache.
-/

namespace MicroCFTA.SourceFlatPruningRecursiveAdmission

open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates SourcePruningRecordTypes SourcePruningEnumerationRecursive
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "FlatCore" => EnumerationFlatState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
universe u v
variable {Typing : Type} {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
local notation "OldResult" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- The original callback derives actual flat rows and the unchanged recursive resource admission. -/
theorem callback_entry
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (flat : FlatCached)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (related : EnumerationFlatCached.Related flat before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (initialMass : mass before.core ≤ ceiling) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (fuel + extra) metadata uv (.inl fragment))
          before.core result after ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (fuel + extra) metadata uv
          (.inl fragment) before.core) = [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → OldResult) stop order,
          SourcePruningEnumerationRecursive.continueWith recur graph templates stop order (fuel + extra)
            metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      mass (EnumerationExpandableIndex.frame after before).core ≤ ceiling ∧
      Fits seed.2 caller.checked ∧
      Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra, ∃ flatAfter,
        SourceFlatPruningOracle.recordTypes graph templates (fuel + extra) metadata uv
          (.inl fragment) flat.core = [.ok (result, flatAfter)] ∧
        EnumerationFlatCached.Related (EnumerationFlatCached.frame flatAfter flat)
          (EnumerationExpandableIndex.frame after before) ∧
        EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap
          (EnumerationFlatCached.frame flatAfter flat) ∧
        (∀ stop order, SourceFlatPruningRestart.decision stop order result.2
          (EnumerationFlatCached.frame flatAfter flat) =
          SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before)) ∧
        ∀ (Out : Type u) (Reason : Type v)
          (callbackFailure : Nat → List (Except Error ((Bool × Metadata Typing) × FlatCore)) → Reason)
          (recur : Metadata Typing → Caller (bits + 2) → Queries → FlatCached → Option Next →
            SourcePruningEnumerationNativeContinuations.HookResult Out Reason (bits + 2)) stop order,
          SourceFlatPruningContinuation.continueWith callbackFailure recur graph templates stop order
            (fuel + extra) metadata uv fragment caller memos.query flat =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationFlatCached.frame flatAfter flat)
              (SourceFlatPruningRestart.decision stop order result.2
                (EnumerationFlatCached.frame flatAfter flat)) := by
  obtain ⟨fuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before
      packet allocated
  have returnedMass : mass (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
    change mass after ≤ ceiling
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
    exact initialMass
  refine ⟨fuel, result, after, returned, stable, frame, types, holes, typing, callback,
    returnedMass, bounded, known, ?_⟩
  intro extra
  obtain ⟨flatAfter, actual, cores⟩ := SourceFlatPruningOracle.recordTypes_replays graph templates
    (fuel + extra) metadata uv (.inl fragment) flat.core before.core result after related.core
      (callback extra).1
  have caches := EnumerationFlatCached.frame_related related cores
  obtain ⟨roots, paths, storage, _realized, counts, flags⟩ := returned.valid
  refine ⟨flatAfter, actual, caches,
    EnumerationFlatNativeIndex.correct_of_related caches caller.checked.native.machine.heap roots paths
      storage.aligned flags counts, ?_, ?_⟩
  · intro stop order
    exact SourceFlatPruningRestart.decision_related caches stop order result.2
  · intro Out Reason callbackFailure recur stop order
    exact SourceFlatPruningContinuation.continueWith_exact callbackFailure recur graph templates stop order
      (fuel + extra) metadata uv fragment caller memos.query flat result flatAfter actual

/-- A completed actual subtree restores the captured packet at its returned caller and full memos. -/
theorem completed_subtree
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (flat : FlatCached) (seed : Seed)
    (outputs : List (Output (bits + 2) Typing)) (reached : Caller (bits + 2)) (queries : Queries)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (related : EnumerationFlatCached.Related flat before)
    (resources : OutcomeResources formulas solver caller seed (.complete outputs reached queries)) :
    ∃ (next : Inventory) (final : Memos),
      Post formulas solver next caller reached final ∧ final.query = queries ∧
      Packet formulas solver next reached final metadata before ∧
      EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap flat ∧
      Fits seed.2 reached.checked ∧
      Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
      ∀ output ∈ outputs, OutputResources formulas solver caller seed output := by
  obtain ⟨next, final, post, saved, captured, bounded, known, outputPackets⟩ :=
    completed_captured_packet formulas solver inventory caller memos metadata before seed
      outputs reached queries packet resources
  obtain ⟨roots, paths, storage, _realized, counts, flags⟩ := captured.valid
  exact ⟨next, final, post, saved, captured,
    EnumerationFlatNativeIndex.correct_of_related related reached.checked.native.machine.heap roots paths
      storage.aligned flags counts, bounded, known, outputPackets⟩

end MicroCFTA.SourceFlatPruningRecursiveAdmission
