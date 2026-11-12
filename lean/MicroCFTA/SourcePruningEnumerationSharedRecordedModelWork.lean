import MicroCFTA.SourcePruningEnumerationSharedRecordedModelProgress
import MicroCFTA.SourcePruningEnumerationNativeWork

/-!
# Work at the same actual recording callback

One callback producer supplies its resource packet and current model.
The same assignment retains its pending size and scalar work.
Both callback verdicts retain the same frame and metadata fields.
The false verdict still requires the current template policy conditions.
This result stops at the callback and restart boundary.
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

/-- One actual callback retains its complete model packet and preserves work. -/
theorem callback_complete_resources_models_work
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
      ((Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
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
        result.1 = false ∧ ∀ group ∈ result.2.pending, SourcePruningResume.Refutes assignment group)) ∧
      EnumerationStorageProgress.pendingSize after assignment =
        EnumerationStorageProgress.pendingSize before.core assignment ∧
      ∀ initialBound,
        SourcePruningEnumerationNativeWork.work initialBound (EnumerationExpandableIndex.frame after before) assignment =
          SourcePruningEnumerationNativeWork.work initialBound before assignment := by
  obtain ⟨fuel, result, after, retained⟩ := callback_complete_resources_models
    formulas solver inventory graph templates metadata uv fragment caller memos before seed
    packet allocated bounded known proper ambient meaning assignment whole satisfied origins
  have resource := retained.1
  rcases resource with ⟨_returned, _stable, framed, _types, _holes, _typing,
    _finalFits, _finalKnown, running⟩
  have observed := (running 0).1
  refine ⟨fuel, result, after, retained, ?_, ?_⟩
  · unfold EnumerationStorageProgress.pendingSize
    rw [framed.values]
  · intro initialBound
    exact SourcePruningEnumerationNativeWork.recordTypes_work initialBound graph templates (fuel + 0)
      metadata uv (.inl fragment) before after result assignment packet.safe.1.total observed

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
