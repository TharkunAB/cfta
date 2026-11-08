import MicroCFTA.SourceSynthesisOriginalVerifiedCompletion
import MicroCFTA.SourceSynthesisOriginalFiniteCapacity

/-!
# Finite enumeration from the same verified original worker return

The original request determines the worker and its returned resource seed.
The worker return supplies the actual caller, global memos and root value.
The driver starts from that return. It does not reset any native cache.
One admission condition joins the worker Room and the driver final Capacity.
Both forecasts use only the original construction and the chosen capacities.

The recursive depth remains an explicit input. Every stopped outcome remains
possible. This theorem does not derive sufficient depth, productivity,
canonical enumeration order, native correspondence or total runtime work.
-/
namespace MicroCFTA.SourceSynthesisOriginalVerifiedFiniteDriver
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue operations inventory globals)
open SourceSynthesisOriginalRankCompletion (seed)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentAllocatedNativeCreditProfile (Capacity)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceSynthesisOriginalFiniteDriver (initialMetadata startup)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationRecursive (Packet OutcomeResources)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "History" => SourceSynthesisHereditaryClosedMemo.History
local notation "NodeFields" => SourceSynthesisHereditaryClosedMemo.NodeFields
local notation "envelope" => SourceCurrentOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentOuterInitialFuel.phaseNeed
local notation "cover" => SourceCurrentInitialSelectionForecast.cover
local notation "finalForecast" => SourcePruningEnumerationFiniteReservation.final
variable {Typing Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Original capacity derives the verified worker and the driver at its same return. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (typing : Typing) (types openHoles : List Nat) (bits budget recursiveFuel : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ _built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      let request : NodeRequest := ⟨emptyValue cache, value⟩
      let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
      let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
      let need := phaseNeed budget first (seed heap)
      let workerSeed := forecast budget first (seed heap)
      (Room bits (cover [output.2.2.2] workerSeed.2) ∧
        Capacity bits (finalForecast recursiveFuel workerSeed 0).2) →
      ∃ result after,
        (∀ fuel, output.1 ≤ fuel →
          nodeCall fuel need need need need need need need need need budget request
            (caller (bits + 2) cache heap) = .done result after) ∧
        ∃ next final, ∃ actual : SourceCurrentAllocatedPartialGraph.NodeCall budget request
            (caller (bits + 2) cache heap) result after,
          SourceCurrentAllocatedPartialSourceReads.NodeCallReads formulas solver actual globals final ∧
          SourceCurrentAllocatedPartialChecks.Checks (SourceCurrentAllocatedPartialChecks.nodeCallTrace actual) ∧
          Post formulas solver next (caller (bits + 2) cache heap) after final ∧
          Available after.checked.native.machine.heap result ∧
          SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧
          SharedReady lib (initialShared after.checked after.merge) ∧
          GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after ∧
          result.free = [] ∧ NodeFields lib literal request result ∧ ValueFields (Origin lib) literal result ∧
          Fits workerSeed.2 after.checked ∧
          SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ workerSeed.1) after.checked.native.machine.heap ∧
          ∃ handle,
            encodeNode result = some handle ∧ lookupNode after.checked.native.machine.heap handle = some result ∧
            Packet formulas solver next after final (initialMetadata typing types openHoles) (startup result handle) ∧
            EnumerationValidity.Canonical (startup result handle).core ∧
            (startup result handle).core.values[0]? = some (.unenumerated (some handle) []) ∧
            SourcePruningEnumerationPrefixAdmission.suspendedBound (startup result handle).core = 0 ∧
            EnumerationCanonicalWaiting.Correct (fun uv => uv) (startup result handle).core.values
              (startup result handle).waiting ∧
            (∀ slot, SourcePruningEnumerationNativeIndex.candidate after.checked.native.machine.heap
              (((startup result handle).core.values[slot]?).getD .eliminated) =
                some ((startup result handle).expandable slot)) ∧
            ∃ bound outcome,
              (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates
                checkEmpty InternedEdgeResidency.nodeEdges stop order (bound + extra) recursiveFuel
                (initialMetadata typing types openHoles) after final.query (startup result handle) = outcome) ∧
              OutcomeResources formulas solver after (finalForecast recursiveFuel workerSeed 0) outcome := by
  obtain ⟨fields, cache, value, heap, built, prepared, complete⟩ :=
    SourceSynthesisOriginalVerifiedCompletion.accepted lib query signed expression returned bits budget formulas solver
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
  let workerSeed := forecast budget first (seed heap)
  have ready : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited := by
    change SourceEqualityConstraintAllocation.Ready _ (emptyValue cache)
    rw [emptySame]
    exact inherited
  have facts := (inventory (ordinarySymbols expression) value heap built).facts
  have frame : Frame formulas solver (inventory (ordinarySymbols expression) value heap built) before.checked :=
    SourceCurrentConstructedOuterInitial.frame formulas solver
      (inventory (ordinarySymbols expression) value heap built) ⟨heap, Cache.emptyState⟩
      (operations cache) (ordinarySymbols expression) value built context.ready rfl
  have bounded : Fits (seed heap).2 before.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap :=
    SourceCurrentConjunctionGuardUniverse.initial heap facts
  refine ⟨fields, cache, value, heap, built, prepared, ?_⟩
  change (Room bits (cover [output.2.2.2] workerSeed.2) ∧
    Capacity bits (finalForecast recursiveFuel workerSeed 0).2) → _
  intro admission
  obtain ⟨result, after, done, next, final, actual, reads, checks, post, resultAvailable, law,
      nextReady, nextProfile, nextHistory, resultClosed, resultFields, recursiveFields⟩ := complete admission.1
  have workerRoom : Room bits workerSeed.2 := admission.1.mono (SourceCurrentInitialSelectionForecast.cover_ge _ _)
  obtain ⟨_otherInventory, _otherMemos, _otherGraph, _otherReads, _otherPost, _otherFrame,
      returnedFits, returnedKnown, _otherAvailable, _otherLaw⟩ :=
    SourceCurrentOuterInitialActual.node_call formulas solver output.1 (request := request) (seed heap)
      context frame bounded known ready available workerRoom (done output.1 (Nat.le_refl _))
  obtain ⟨handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags⟩ :=
    SourcePruningEnumerationRecursive.initial_packet formulas solver next after final
      (initialMetadata typing types openHoles) result post.context resultAvailable resultClosed rfl
  have reserved := SourcePruningEnumerationFiniteReservation.reserved_of_final_capacity
    bits recursiveFuel workerSeed 0 admission.2
  obtain ⟨bound, outcome, running, resources⟩ :=
    SourcePruningEnumerationRecursive.run_finite_complete_resources
      holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges stop order
      formulas solver recursiveFuel next after final (startup result handle)
      (initialMetadata typing types openHoles) workerSeed 0 packet returnedFits returnedKnown
      (fun _ _ _ _ _ member => member) (fun _ _ _ _ => Nat.le_refl _) (Nat.le_of_eq suspended) reserved
  exact ⟨result, after, done, next, final, actual, reads, checks, post, resultAvailable, law,
    nextReady, nextProfile, nextHistory, resultClosed, resultFields, recursiveFields,
    returnedFits, returnedKnown, handle, encoded, decoded, packet, canonical, stored, suspended, waiting,
    flags, bound, outcome, running, resources⟩

end MicroCFTA.SourceSynthesisOriginalVerifiedFiniteDriver
