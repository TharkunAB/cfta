import MicroCFTA.SourceSynthesisOriginalHereditarySharedCompletion
import MicroCFTA.SourceCurrentSharedOuterInitialLiteralRanges
import MicroCFTA.SourceCurrentAllocatedSharedPartialChecksFromRanges
import MicroCFTA.SourceCurrentAllocatedSharedPartialRangesFromChecks

/-!
# Original hereditary shared completion with literal checks

One existing original completion supplies the build, preparation, caller,
result and full endpoint certificates. Those same source witnesses derive
current initialization facts for the literal base-bound range plan.
The combined capacity test supplies the base schedule's room.

Every larger sufficient outer fuel retains the same endpoint metadata.
The base run supplies graph checks. Those checks and each actual larger
successful run derive its literal ranges. No larger schedule room is used.
Original native capacity,
complete enumeration and Haskell correspondence remain separate.
-/
namespace MicroCFTA.SourceSynthesisOriginalCheckedHereditarySharedCompletion
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedSharedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue checked operations inventory globals)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "History" => SourceSynthesisHereditaryClosedMemo.History
local notation "NodeFields" => SourceSynthesisHereditaryClosedMemo.NodeFields
local notation "envelope" => SourceCurrentSharedOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
local notation "cover" => SourceCurrentInitialSelectionForecast.cover
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- One original completion retains its endpoint, graph checks and every sufficient run's literal ranges. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression) (bits budget : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ _built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      let request : NodeRequest := ⟨emptyValue cache, value⟩
      let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
      let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
      let need := phaseNeed budget first (seed heap)
      Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) →
      ∃ result after,
        SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
          output.1 need need need need need need need need need budget request
          (caller (bits + 2) cache heap) ∧
        (∀ fuel, output.1 ≤ fuel →
          nodeCall fuel need need need need need need need need need budget request
            (caller (bits + 2) cache heap) = .done result after) ∧
        (∀ fuel, output.1 ≤ fuel →
          SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
            fuel need need need need need need need need need budget request
            (caller (bits + 2) cache heap)) ∧
        ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.NodeCall budget request
            (caller (bits + 2) cache heap) result after,
          SourceCurrentAllocatedSharedPartialChecks.Checks
            (SourceCurrentAllocatedSharedPartialChecks.nodeCallTrace graph) ∧
          SourceCurrentAllocatedSharedPartialEndpointReads.NodeCallReads formulas solver graph globals final ∧
          Post formulas solver next (caller (bits + 2) cache heap) after final ∧
          Frame formulas solver next after.checked ∧
          Fits (forecast budget first (seed heap)).2 after.checked ∧
          SourceEqualityAnnotationHeap.Heap
            (fun guard => guard ∈ (forecast budget first (seed heap)).1) after.checked.native.machine.heap ∧
          Available after.checked.native.machine.heap result ∧
          SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧
          SharedReady lib (initialShared after.checked after.merge) ∧
          GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after ∧
          result.free = [] ∧ NodeFields lib literal request result ∧ ValueFields (Origin lib) literal result := by
  obtain ⟨fields, cache, value, heap, built, prepared, complete⟩ :=
    SourceSynthesisOriginalHereditarySharedCompletion.accepted
      lib query signed expression returned bits budget formulas solver
  have initialized := SourceCurrentAllocatedPartialInitialization.constructed (bits + 2)
    prepared.history Cache.empty_valid (ordinarySymbols expression) (fun _ member => member)
    value heap built formulas solver
  have context := initialized.1
  obtain ⟨_identity, emptySame, inherited, available, _closed, _original⟩ := initialized.2
  let before := caller (bits + 2) cache heap
  let request : NodeRequest := ⟨emptyValue cache, value⟩
  let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
  let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request before
  let need := phaseNeed budget first (seed heap)
  have ready : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited := by
    change SourceEqualityConstraintAllocation.Ready _ (emptyValue cache)
    rw [emptySame]
    exact inherited
  have facts := (inventory (ordinarySymbols expression) value heap built).facts
  have frame : Frame formulas solver (inventory (ordinarySymbols expression) value heap built) before.checked :=
    SourceCurrentConstructedOuterInitial.frame formulas solver
      (inventory (ordinarySymbols expression) value heap built) ⟨heap, Cache.emptyState⟩
      (operations cache) (ordinarySymbols expression) value built context.ready rfl
  have fits : Fits (seed heap).2 before.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap :=
    SourceCurrentConjunctionGuardUniverse.initial heap facts
  refine ⟨fields, cache, value, heap, built, prepared, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, done, next, final, graph, metadata⟩ := complete room
  have rootRoom : Room bits (forecast budget first (seed heap)).2 :=
    room.mono (SourceCurrentInitialSelectionForecast.cover_ge _ _)
  have checkedBase : SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
      output.1 need need need need need need need need need budget request before :=
    SourceCurrentSharedOuterInitialLiteralRanges.node_call formulas solver output.1 (seed heap)
      context frame fits known ready available rootRoom
  have checkedGraph := SourceCurrentAllocatedSharedPartialChecksFromRanges.node_call
    checkedBase (done output.1 (Nat.le_refl _)) graph
  have checkedRuns : ∀ fuel, output.1 ≤ fuel →
      SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
        fuel need need need need need need need need need budget request before := by
    intro fuel enough
    exact SourceCurrentAllocatedSharedPartialRangesFromChecks.node_call
      (graph := graph) checkedGraph (done fuel enough)
  exact ⟨result, after, checkedBase, done, checkedRuns, next, final, graph, checkedGraph, metadata⟩

end MicroCFTA.SourceSynthesisOriginalCheckedHereditarySharedCompletion
