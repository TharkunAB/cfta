import MicroCFTA.SourceSynthesisOriginalSharedRankCompletion
import MicroCFTA.SourceSynthesisHereditarySharedOuterTraversal
import MicroCFTA.SourceSynthesisOriginalHereditaryProgramFields
import MicroCFTA.SourceSynthesisOriginalTypeSharedState
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

/-!
# Original shared completion with complete hereditary fields

One original build and allocation preparation determine the cold caller.
Its actual stable rank completion supplies one result and returned caller.
Original construction derives every initial field, Type state, guard and
memo-history certificate for that same caller. The base completed call
then supplies one graph, canonical read bundle and complete caller Post.
Stable execution retains that same endpoint at every larger outer bound.

Only the computed initial capacity condition remains. It bounds the base
schedule. This proof does not require capacity for larger fuel schedules.
It does not prove that native fixed-width execution satisfies the test.
Failed prefixes, complete enumeration, total driver work, native CAF
initialization and Haskell sharing correspondence remain separate.
-/
namespace MicroCFTA.SourceSynthesisOriginalHereditarySharedCompletion
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

/-- Original input and computed capacity construct the same fully verified recursive return. -/
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
        (∀ fuel, output.1 ≤ fuel →
          nodeCall fuel need need need need need need need need need budget request
            (caller (bits + 2) cache heap) = .done result after) ∧
        ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.NodeCall budget request
            (caller (bits + 2) cache heap) result after,
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
    SourceSynthesisOriginalSharedRankCompletion.accepted lib query signed expression returned bits budget formulas solver
  have initialized := SourceCurrentAllocatedPartialInitialization.constructed (bits + 2)
    prepared.history Cache.empty_valid (ordinarySymbols expression) (fun _ member => member)
    value heap built formulas solver
  have context := initialized.1
  obtain ⟨_identity, emptySame, inherited, available, closed, _original⟩ := initialized.2
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
  have sourceFields := SourceSynthesisOriginalHereditaryProgramFields.firstOrderRaw_fields
    lib query signed expression returned value heap built
  have typedState : SharedReady lib (initialShared before.checked before.merge) :=
    SourceSynthesisOriginalTypeSharedState.initial_ready lib query signed expression returned value heap built
      (bits + 2) (operations cache) context.ready.good
  have profile : GuardHeap (Origin lib) heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentConstrainedCapGuardExecution.closed_heap (Origin lib) (ordinarySymbols expression)
  have history : History lib literal before :=
    SourceSynthesisHereditaryClosedMemo.initial lib literal (checked (bits + 2) cache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  refine ⟨fields, cache, value, heap, built, prepared, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, done, _available, _law⟩ := complete room
  have rootRoom : Room bits (forecast budget first (seed heap)).2 :=
    room.mono (SourceCurrentInitialSelectionForecast.cover_ge _ _)
  obtain ⟨next, final, graph, reads, post, afterFrame, afterFits, afterKnown,
      resultAvailable, law, nextReady, nextProfile, nextHistory, resultClosed, resultFields⟩ :=
    SourceSynthesisHereditarySharedOuterTraversal.nodeCall_fields lib literal formulas solver (seed heap)
      (request := request) context frame fits known typedState profile history ready available closed
      (Or.inr sourceFields) rootRoom (done output.1 (Nat.le_refl _))
  exact ⟨result, after, done, next, final, graph, reads, post, afterFrame, afterFits, afterKnown,
    resultAvailable, law, nextReady, nextProfile, nextHistory, resultClosed, resultFields,
    resultFields.program sourceFields⟩

end MicroCFTA.SourceSynthesisOriginalHereditarySharedCompletion
