import MicroCFTA.SourcePruningEnumerationFiniteResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationExecutionExpansionBridge

/-!
# Original-input paths for both finite-depth enumeration workers

Depth induction supplies every smaller worker.
No future worker, stage, trace or completion supplier remains in the public inputs.
One common larger work bound retains each stable outcome and its resources.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionWorkerPaths.Native
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

open SourcePruningEnumerationRecursive
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)

/-- Original inputs derive all actual paths at every finite recursive depth. -/
theorem run_finite_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop) (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling).1 P) :
    ∃ bound, ∀ extra,
      SourcePruningEnumerationExecutionPaths.Native P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel metadata caller memos.query before := by
  revert inventory caller memos before metadata seed ceiling
  induction recursiveFuel with
  | zero =>
      intro _inventory caller memos before metadata _seed _ceiling
        _packet _bounded _known _initialMass _reserved original _projected
      refine ⟨0, ?_⟩
      intro extra
      exact SourcePruningEnumerationExecutionPaths.resume_native_zero_paths P
        holeKey fits admits graph templates checkEmpty edgesOf stop order (0 + extra)
        metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) original
  | succ recursiveFuel ih =>
      intro inventory caller memos before metadata seed ceiling
        packet bounded known initialMass reserved original projected
      cases chosen : SourcePruningEnumerationRestart.decision stop order metadata before with
      | none =>
          refine ⟨0, ?_⟩
          intro extra
          unfold SourcePruningEnumerationExecutionPaths.Native
          rw [chosen]
          refine ⟨original, ?_, True.intro⟩
          intro output member
          cases List.mem_singleton.mp member
          exact original
      | some selected =>
          cases selected with
          | done =>
              refine ⟨0, ?_⟩
              intro extra
              unfold SourcePruningEnumerationExecutionPaths.Native
              rw [chosen]
              refine ⟨original, ?_, True.intro⟩
              intro output member
              cases List.mem_singleton.mp member
              exact original
          | stuck =>
              refine ⟨0, ?_⟩
              intro extra
              unfold SourcePruningEnumerationExecutionPaths.Native
              rw [chosen]
              refine ⟨original, ?_, True.intro⟩
              intro output member
              cases member
          | expand uv =>
              obtain ⟨bound, _outcome, _running, _resources, paths⟩ :=
                SourcePruningEnumerationExecutionExpansionBridge.Native.selected_finite_complete_resources_paths
                  holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
                  (SourcePruningEnumerationRecursive.finite_complete
                    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel)
                  inventory caller memos before metadata uv seed ceiling packet bounded known
                  selectionMembers selectionLength initialMass reserved chosen P original tails projected
                  (by
                    intro nextInventory nextCaller nextMemos nextCache nextMetadata nextSeed nextCeiling
                      nextPacket nextBounded nextKnown _nextMembers _nextLength nextMass nextReserved nextPaths nextProjected
                    exact ih nextInventory nextCaller nextMemos nextCache nextMetadata nextSeed nextCeiling
                      nextPacket nextBounded nextKnown nextMass nextReserved nextPaths nextProjected)
              refine ⟨bound, ?_⟩
              intro extra
              simpa only [SourcePruningEnumerationExecutionPaths.Native, chosen] using paths extra

/-- One stable actual outcome keeps its resources and all execution paths at the same work bound. -/
theorem run_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop) (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling).1 P) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra, SourcePruningEnumerationExecutionPaths.Native P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel metadata caller memos.query before) := by
  obtain ⟨resourceBound, outcome, running, resources⟩ := SourcePruningEnumerationRecursive.run_finite_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel inventory
    caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved
  obtain ⟨pathBound, paths⟩ := run_finite_paths
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel inventory
    caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved
    P original tails projected
  refine ⟨resourceBound + pathBound, outcome, ?_, resources, ?_⟩
  · intro extra
    simpa only [Nat.add_assoc] using running (pathBound + extra)
  · intro extra
    have current := paths (resourceBound + extra)
    have same : pathBound + (resourceBound + extra) = resourceBound + pathBound + extra := by omega
    rw [same] at current
    exact current

end MicroCFTA.SourcePruningEnumerationExecutionWorkerPaths.Native

namespace MicroCFTA.SourcePruningEnumerationExecutionWorkerPaths.Prepared
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

open SourcePruningEnumerationPreparedRecursive
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)

/-- Original inputs derive all actual paths at every finite recursive depth. -/
theorem run_finite_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop) (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling).1 P) :
    ∃ bound, ∀ extra,
      SourcePruningEnumerationExecutionPaths.Prepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel metadata caller memos.query before := by
  revert inventory caller memos before metadata seed ceiling
  induction recursiveFuel with
  | zero =>
      intro _inventory caller memos before metadata _seed _ceiling
        _packet _bounded _known _initialMass _reserved original _projected
      refine ⟨0, ?_⟩
      intro extra
      exact SourcePruningEnumerationExecutionPaths.resume_prepared_zero_paths P
        holeKey fits admits graph templates checkEmpty edgesOf stop order (0 + extra)
        metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) original
  | succ recursiveFuel ih =>
      intro inventory caller memos before metadata seed ceiling
        packet bounded known initialMass reserved original projected
      cases chosen : SourcePruningEnumerationRestart.decision stop order metadata before with
      | none =>
          refine ⟨0, ?_⟩
          intro extra
          unfold SourcePruningEnumerationExecutionPaths.Prepared
          rw [chosen]
          refine ⟨original, ?_, True.intro⟩
          intro output member
          cases List.mem_singleton.mp member
          exact original
      | some selected =>
          cases selected with
          | done =>
              refine ⟨0, ?_⟩
              intro extra
              unfold SourcePruningEnumerationExecutionPaths.Prepared
              rw [chosen]
              refine ⟨original, ?_, True.intro⟩
              intro output member
              cases List.mem_singleton.mp member
              exact original
          | stuck =>
              refine ⟨0, ?_⟩
              intro extra
              unfold SourcePruningEnumerationExecutionPaths.Prepared
              rw [chosen]
              refine ⟨original, ?_, True.intro⟩
              intro output member
              cases member
          | expand uv =>
              obtain ⟨bound, _outcome, _running, _resources, paths⟩ :=
                SourcePruningEnumerationExecutionExpansionBridge.Prepared.selected_finite_complete_resources_paths
                  holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
                  (SourcePruningEnumerationPreparedRecursive.finite_complete
                    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel)
                  inventory caller memos before metadata uv seed ceiling packet bounded known
                  selectionMembers selectionLength initialMass reserved chosen P original tails projected
                  (by
                    intro nextInventory nextCaller nextMemos nextCache nextMetadata nextSeed nextCeiling
                      nextPacket nextBounded nextKnown _nextMembers _nextLength nextMass nextReserved nextPaths nextProjected
                    exact ih nextInventory nextCaller nextMemos nextCache nextMetadata nextSeed nextCeiling
                      nextPacket nextBounded nextKnown nextMass nextReserved nextPaths nextProjected)
              refine ⟨bound, ?_⟩
              intro extra
              simpa only [SourcePruningEnumerationExecutionPaths.Prepared, chosen] using paths extra

/-- One stable actual outcome keeps its resources and all execution paths at the same work bound. -/
theorem run_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop) (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling).1 P) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra, SourcePruningEnumerationExecutionPaths.Prepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel metadata caller memos.query before) := by
  obtain ⟨resourceBound, outcome, running, resources⟩ := SourcePruningEnumerationPreparedRecursive.run_finite_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel inventory
    caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved
  obtain ⟨pathBound, paths⟩ := run_finite_paths
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel inventory
    caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved
    P original tails projected
  refine ⟨resourceBound + pathBound, outcome, ?_, resources, ?_⟩
  · intro extra
    simpa only [Nat.add_assoc] using running (pathBound + extra)
  · intro extra
    have current := paths (resourceBound + extra)
    have same : pathBound + (resourceBound + extra) = resourceBound + pathBound + extra := by omega
    rw [same] at current
    exact current

end MicroCFTA.SourcePruningEnumerationExecutionWorkerPaths.Prepared
