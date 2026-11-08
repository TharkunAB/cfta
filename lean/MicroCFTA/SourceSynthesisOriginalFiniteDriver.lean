import MicroCFTA.SourceSynthesisOriginalCallerInitialization
import MicroCFTA.SourcePruningEnumerationInitialPacket
import MicroCFTA.SourcePruningEnumerationFiniteResources
import MicroCFTA.SourceCurrentConjunctionGuardUniverse

/-!
# Finite recursive enumeration from accepted source input

Accepted source input derives its Label build, equality preparation and
cold caller. Literal metadata has no pending checks. The actual handle
readback derives the startup packet and its zero suspended-mass bound.
One Room test for the chosen recursive depth supplies every reservation.

The result retains all stopped outcomes. The theorem does not derive a
recursive depth that avoids stops, a native word bound, or total work.
Policy values and their graph remain explicit. The stored nodeEdges
getter is included. Canonical and weighted public order are separate.
The theorem does not identify modeled handles with native node IDs.
-/
namespace MicroCFTA.SourceSynthesisOriginalFiniteDriver
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialInitialization (caller inventory globals)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationRecursive (Packet OutcomeResources)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Actual initial records supply the guard list and payload-mass forecast. -/
def seed (heap : InternedConstructorTemplates.State Symbol Guard) : Seed :=
  (SourceCurrentConjunctionGuardUniverse.guards heap,
    ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)

/-- The supplied initial metadata values have no pending template checks. -/
def initialMetadata (typing : Typing) (types openHoles : List Nat) : Metadata Typing :=
  ⟨[], types, openHoles, typing⟩

/-- The startup retains the literal root slot and its native expandable flag. -/
def startup (value : Node) (handle : Nat) : Cached :=
  ⟨EnumerationState.initial handle,
    fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
    fun _ => none⟩

/-- Source input derives finite driver admission, including the literal stored-row getter. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (typing : Typing) (types openHoles : List Nat) (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      Context formulas solver (inventory (ordinarySymbols expression) value heap built)
        (caller (bits + 2) cache heap) globals ∧
      InternedNestedFacts.Facts heap ∧ Available heap value ∧ value.free = [] ∧
      ∃ handle,
        encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
        Packet formulas solver (inventory (ordinarySymbols expression) value heap built)
          (caller (bits + 2) cache heap) globals (initialMetadata typing types openHoles)
          (startup value handle) ∧
        EnumerationValidity.Canonical (startup value handle).core ∧
        (startup value handle).core.values[0]? = some (.unenumerated (some handle) []) ∧
        SourcePruningEnumerationPrefixAdmission.suspendedBound (startup value handle).core = 0 ∧
        EnumerationCanonicalWaiting.Correct (fun uv => uv) (startup value handle).core.values
          (startup value handle).waiting ∧
        (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
          (((startup value handle).core.values[slot]?).getD .eliminated) =
            some ((startup value handle).expandable slot)) ∧
        Fits (seed heap).2 (caller (bits + 2) cache heap).checked ∧
        SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap ∧
        (∀ (edgesOf : Node → List (EdgeValue Symbol Guard)),
          (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
          (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
          ∀ recursiveFuel,
            Room bits (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0).2 →
            ∃ bound outcome,
              (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates
                checkEmpty edgesOf stop order (bound + extra) recursiveFuel
                (initialMetadata typing types openHoles) (caller (bits + 2) cache heap) globals.query
                (startup value handle) = outcome) ∧
              OutcomeResources formulas solver (caller (bits + 2) cache heap)
                (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0) outcome) ∧
        (∀ recursiveFuel,
          Room bits (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0).2 →
          ∃ bound outcome,
            (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates
              checkEmpty InternedEdgeResidency.nodeEdges stop order (bound + extra) recursiveFuel
              (initialMetadata typing types openHoles) (caller (bits + 2) cache heap) globals.query
              (startup value handle) = outcome) ∧
            OutcomeResources formulas solver (caller (bits + 2) cache heap)
              (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0) outcome) := by
  obtain ⟨fields, cache, value, heap, built, prepared, context, facts, available, _roles,
      _growth, _history, _identity, _emptySame, _inherited, closed, _original⟩ :=
    SourceSynthesisOriginalCallerInitialization.accepted lib query signed expression returned (bits + 2)
      Cache.emptyState Cache.empty_valid formulas solver
  obtain ⟨handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags⟩ :=
    SourcePruningEnumerationRecursive.initial_packet formulas solver
      (inventory (ordinarySymbols expression) value heap built) (caller (bits + 2) cache heap)
      globals (initialMetadata typing types openHoles) value context available closed rfl
  have bounded : Fits (seed heap).2 (caller (bits + 2) cache heap).checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap :=
    SourceCurrentConjunctionGuardUniverse.initial heap facts
  have complete : ∀ (edgesOf : Node → List (EdgeValue Symbol Guard)),
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      ∀ recursiveFuel,
        Room bits (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0).2 →
        ∃ bound outcome,
          (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates
            checkEmpty edgesOf stop order (bound + extra) recursiveFuel
            (initialMetadata typing types openHoles) (caller (bits + 2) cache heap) globals.query
            (startup value handle) = outcome) ∧
          OutcomeResources formulas solver (caller (bits + 2) cache heap)
            (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0) outcome := by
    intro edgesOf members length recursiveFuel room
    exact SourcePruningEnumerationRecursive.run_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
      (inventory (ordinarySymbols expression) value heap built) (caller (bits + 2) cache heap) globals
      (startup value handle) (initialMetadata typing types openHoles) (seed heap) 0
      packet bounded known members length (Nat.le_of_eq suspended)
      (SourcePruningEnumerationFiniteReservation.reserved_of_final_room bits recursiveFuel (seed heap) 0 room)
  refine ⟨fields, cache, value, heap, built, prepared, context, facts, available, closed,
    handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags, bounded, known,
    complete, ?_⟩
  exact complete InternedEdgeResidency.nodeEdges (fun _ _ _ _ _ member => member)
    (fun _ _ _ _ => Nat.le_refl _)

end MicroCFTA.SourceSynthesisOriginalFiniteDriver
