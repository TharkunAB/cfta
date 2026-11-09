import MicroCFTA.SourcePruningEnumerationSharedHookCertificates
import MicroCFTA.SourcePruningCallbackCompletion
import MicroCFTA.SourcePruningCallbackExact

/-!
# Current resources at the actual shared fragment callback

The current packet derives the complete Left callback return.
Both pruning and continuation use that same metadata and observed core.
The callback retains the native caller, query memos and original seed.
This law does not execute a recursive continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Current callback inputs derive one stable return and its exact shared continuation. -/
theorem callback_complete_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧
      Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
            stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) := by
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨fuel, result, after, success, stable, frame, afterOrder, types, holes, typing, pendingBound⟩ :=
    recordTypes_inl_complete_bounded graph templates level frontier metadata uv fragment before.core
      packet.safe ordered allocated packet.bounded
  refine ⟨fuel, result, after,
    SourcePruningEnumerationRecursive.callback_frame packet result.2 after stable.safe frame
      ⟨level, frontier, afterOrder⟩ pendingBound,
    stable, frame, types, holes, typing, bounded, known, ?_⟩
  intro extra
  have more := recordTypes_moreFuel graph templates fuel extra metadata uv (.inl fragment)
    before.core result after success
  have exactRaw := SourcePruningCallbackExact.recordTypes_exact graph templates (fuel + extra)
    metadata uv (.inl fragment) before.core after result more
  refine ⟨more, exactRaw, ?_⟩
  intro recur stop order
  unfold continueWith
  rw [exactRaw]
  obtain ⟨flag, updated⟩ := result
  cases flag <;> rfl

end MicroCFTA.SourcePruningEnumerationSharedRecursive
