import MicroCFTA.SourceSynthesisOriginalFiniteDriver
import MicroCFTA.SourcePruningEnumerationFiniteCapacity

/-!
# Source finite-driver admission from final counter capacity

Accepted source input supplies the same actual startup as the earlier
finite-driver theorem. Final counter capacity reserves every native entry
through its completed-step forecast. All stopped outcomes remain explicit.
The theorem does not choose sufficient depth or identify the public native
policy, lazy demand, or fixed-width allocation with this model.
-/
namespace MicroCFTA.SourceSynthesisOriginalFiniteDriver
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialInitialization (caller inventory globals)
open SourceCurrentAllocatedNativeCreditProfile (Capacity)
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

/-- Source input derives finite driver admission, including the literal stored-row getter. -/
theorem accepted_capacity
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
            Capacity bits (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0).2 →
            ∃ bound outcome,
              (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates
                checkEmpty edgesOf stop order (bound + extra) recursiveFuel
                (initialMetadata typing types openHoles) (caller (bits + 2) cache heap) globals.query
                (startup value handle) = outcome) ∧
              OutcomeResources formulas solver (caller (bits + 2) cache heap)
                (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0) outcome) ∧
        (∀ recursiveFuel,
          Capacity bits (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0).2 →
          ∃ bound outcome,
            (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates
              checkEmpty InternedEdgeResidency.nodeEdges stop order (bound + extra) recursiveFuel
              (initialMetadata typing types openHoles) (caller (bits + 2) cache heap) globals.query
              (startup value handle) = outcome) ∧
            OutcomeResources formulas solver (caller (bits + 2) cache heap)
              (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0) outcome) := by
  obtain ⟨fields, cache, value, heap, built, prepared, context, facts, available, closed,
      handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags,
      bounded, known, _oldSelectors, _oldInterned⟩ :=
    accepted lib query signed expression returned holeKey fits admits graph templates checkEmpty stop order
      typing types openHoles bits formulas solver
  have complete : ∀ (edgesOf : Node → List (EdgeValue Symbol Guard)),
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      ∀ recursiveFuel,
        Capacity bits (SourcePruningEnumerationFiniteReservation.final recursiveFuel (seed heap) 0).2 →
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
      (SourcePruningEnumerationFiniteReservation.reserved_of_final_capacity bits recursiveFuel (seed heap) 0 room)
  refine ⟨fields, cache, value, heap, built, prepared, context, facts, available, closed,
    handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags, bounded, known,
    complete, ?_⟩
  exact complete InternedEdgeResidency.nodeEdges (fun _ _ _ _ _ member => member)
    (fun _ _ _ _ => Nat.le_refl _)

end MicroCFTA.SourceSynthesisOriginalFiniteDriver
