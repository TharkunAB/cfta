import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryCanonicalArity
import MicroCFTA.SourcePruningEnumerationPreparedFiniteProjectionHeap

/-!
# Original histories, canonical storage, arity and projection at one outcome

The original finite resource producer supplies each actual output history.
The history preserves canonical stored suspended tries through every branch.
The result retains the same bound, outcome, native resources and histories.
A common larger work bound identifies the projection producer outcome.
Original caller projection supplies each output and exposed endpoint projection.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationValidity InternedConstructorTemplates
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

/-- Original finite resources and canonical storage derive canonicality at every actual output. -/
theorem run_finite_complete_resources_with_history_canonical_arity_projection_heap
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
      caller.checked.native.machine.heap) :
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
      OutcomeProjectionHeap outcome := by
  obtain ⟨bound, outcome, running, resources, histories, canonicalOutputs, arity⟩ :=
    run_finite_complete_resources_with_history_canonical_arity
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
      inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved canonical initialArity
  obtain ⟨projectionBound, projectionOutcome, projectionRunning, _projectionResources, projected⟩ :=
    run_finite_complete_resources_with_projection_heap
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
      inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved initialProjection
  have projectionAt := projectionRunning bound
  rw [Nat.add_comm projectionBound bound] at projectionAt
  have same : projectionOutcome = outcome := projectionAt.symm.trans (running projectionBound)
  rw [same] at projected
  exact ⟨bound, outcome, running, resources, histories, canonicalOutputs, arity, projected⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
