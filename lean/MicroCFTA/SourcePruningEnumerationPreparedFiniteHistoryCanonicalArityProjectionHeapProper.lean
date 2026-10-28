import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryCanonicalArityProjectionHeap
import MicroCFTA.SourcePruningEnumerationPreparedResourceHistoryProper

/-!
# Proper storage at the same complete prepared finite outcome

The original resource producer retains its bound and outcome.
Each actual output history preserves initial proper storage.
The result retains all earlier resources, histories, arity and projection.
This output invariant does not assert that an output exists.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationValidity EnumerationProgress InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
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

/-- Initial proper storage reaches each output of the same full finite resource producer. -/
theorem run_finite_complete_resources_with_history_canonical_arity_projection_heap_proper
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
    (canonical : Canonical before.core)
    (initialArity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap)
    (initialProjection : Heap
      (fun constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
      caller.checked.native.machine.heap)
    (proper : ProperState before.core) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        Canonical output.cache.core) ∧
      OutcomeResourcesWithArity formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      OutcomeProjectionHeap outcome ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        ProperState output.cache.core) := by
  obtain ⟨bound, outcome, running, resources, histories, canonicalOutputs, arity, projected⟩ :=
    run_finite_complete_resources_with_history_canonical_arity_projection_heap
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
      inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved canonical initialArity initialProjection
  exact ⟨bound, outcome, running, resources, histories, canonicalOutputs, arity, projected,
    fun output member => (histories 0 output member).proper_output proper⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
