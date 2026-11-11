import MicroCFTA.SourcePruningEnumerationSharedPreparedCallbackResources
import MicroCFTA.SourcePruningEnumerationPreparedCallbackProgress
import MicroCFTA.SourcePruningEnumerationPolicyOrigins

/-!
# Models at the actual shared recording callback

The current resource producer supplies one callback result and its frame.
The same assignment retains its model, original paths and proper storage.
The pruning verdict requires separate template policies.
This law does not execute the recursive continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open EnumerationProgress InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationOrigins (AssignmentOrigins)
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
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Retain the shared callback resource packet and its same-assignment model progress. -/
theorem callback_complete_resources_models
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (proper : ProperState before.core)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Language.Term Symbol → Prop)
    (assignment : Nat → Language.Term Symbol) (whole : Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap) meaning assignment before.core)
    (origins : AssignmentOrigins whole before.core.counter assignment) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
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
                (EnumerationExpandableIndex.frame after before))) ∧
      ProperState after ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) meaning assignment after ∧
      AssignmentOrigins whole after.counter assignment ∧
      (∀ (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat),
        SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame after before) ≠ some .stuck) ∧
      (templates = [] → result.1 = false) ∧
      (uv < before.core.counter → Fragments.fill assignment fragment = assignment uv →
        SourcePruningTemplates.OriginPolicies templates whole →
        (∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group) →
        result.1 = false ∧ ∀ group ∈ result.2.pending, SourcePruningResume.Refutes assignment group) := by
  obtain ⟨fuel, result, after, returned, stable, framed, types, holes, typing,
    finalFits, finalKnown, running⟩ := callback_complete_resources
      formulas solver inventory graph templates metadata uv fragment caller memos before seed
      packet allocated bounded known
  have properAfter : ProperState after := by
    simpa only [ProperState, framed.values] using proper
  have satisfiedAfter := (SourcePruningEnumerationNativeLanguage.satisfies_frame
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap) meaning assignment before.core after framed).mpr satisfied
  have observed := (running 0).1
  refine ⟨fuel, result, after,
    ⟨returned, stable, framed, types, holes, typing, finalFits, finalKnown, running⟩,
    properAfter, satisfiedAfter, ?_, ?_, ?_, ?_⟩
  · simpa only [framed.counter] using origins
  · intro stop order
    exact (SourcePruningEnumerationPreparedRecursive.callback_record_progress
      formulas solver inventory graph templates metadata uv fragment caller memos before stop order
      (fuel + 0) result after packet allocated proper observed ambient meaning assignment satisfied).2.2.2.2.2
  · intro empty
    have pureRead := observed
    rw [empty, recordTypes_empty] at pureRead
    exact congrArg Prod.fst ((success_pure _ result before.core after).mp pureRead).1
  · intro inside filled policies refuted
    exact SourcePruningRecordTypes.recordTypes_inl_refutes_of_origin graph
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap) meaning assignment assignment templates whole
      (fuel + 0) uv before.core.counter metadata fragment before.core after result packet.safe.1.total
      satisfied filled policies (origins uv inside) packet.bounded (fun _ _ => rfl) refuted observed

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
