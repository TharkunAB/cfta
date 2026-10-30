import MicroCFTA.SourcePruningEnumerationExecutionWorkerPaths
import MicroCFTA.SourcePruningEnumerationClosedForecastPaths

/-!
# Original finite paths through both recursive workers

The original alphabet supplies the same finite path carrier at every depth.
Each worker retains its stable outcome and the computed resource forecast.
-/

namespace MicroCFTA.SourcePruningEnumerationExecutionOriginalPaths.Native
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

/-- Both resource and actual execution path guarantees use one original finite carrier. -/
theorem run_original_finite_complete_resources_paths
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
    (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (included : seed.1 ⊆ SourceCurrentNativeClosedGuardAlphabet.originalAlphabet literals) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra, SourcePruningEnumerationExecutionPaths.Native (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier
          (SourceCurrentNativeClosedGuardAlphabet.originalAlphabet literals) before.core) holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel metadata caller memos.query before) := by
  exact SourcePruningEnumerationExecutionWorkerPaths.Native.run_finite_complete_resources_paths
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel inventory
    caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved
    (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier
          (SourceCurrentNativeClosedGuardAlphabet.originalAlphabet literals) before.core)
    (SourcePruningEnumerationForecastPathDomain.initial_paths _ _)
    (SourcePruningEnumerationForecastPathDomain.tail_closed _ _)
    (SourcePruningEnumerationClosedForecastPaths.native_original_paths
      literals normalized before.core recursiveFuel seed ceiling included)

end MicroCFTA.SourcePruningEnumerationExecutionOriginalPaths.Native

namespace MicroCFTA.SourcePruningEnumerationExecutionOriginalPaths.Prepared
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

/-- Both resource and actual execution path guarantees use one original finite carrier. -/
theorem run_original_finite_complete_resources_paths
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
    (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (included : seed.1 ⊆ SourceCurrentNativeClosedGuardAlphabet.originalAlphabet literals) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra, SourcePruningEnumerationExecutionPaths.Prepared (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier
          (SourceCurrentNativeClosedGuardAlphabet.originalAlphabet literals) before.core) holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel metadata caller memos.query before) := by
  exact SourcePruningEnumerationExecutionWorkerPaths.Prepared.run_finite_complete_resources_paths
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel inventory
    caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved
    (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier
          (SourceCurrentNativeClosedGuardAlphabet.originalAlphabet literals) before.core)
    (SourcePruningEnumerationForecastPathDomain.initial_paths _ _)
    (SourcePruningEnumerationForecastPathDomain.tail_closed _ _)
    (SourcePruningEnumerationClosedForecastPaths.prepared_original_paths
      literals normalized before.core recursiveFuel seed ceiling included)

end MicroCFTA.SourcePruningEnumerationExecutionOriginalPaths.Prepared
