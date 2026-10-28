import MicroCFTA.SourcePruningEnumerationFiniteHistoryResources
import MicroCFTA.SourcePruningEnumerationFiniteResourcesArity
import MicroCFTA.SourcePruningEnumerationHistoryOutputArity

/-!
# Original finite histories with derived projected arity

The original history producer and the arity producer each run once.
A common work bound identifies their same actual outcome.
Every actual output heap supplies all arity annotations on that output's
original history. No future heap or history annotation is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
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
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Keep every original finite result field and derive arity on each same-bound actual output history. -/
theorem run_finite_complete_resources_with_history_arity
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
    (arity : ArityHeap caller.checked.native.machine.heap) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      OutcomeResourcesWithArity formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output := by
  obtain ⟨historyBound, outcome, running, resources, histories⟩ :=
    run_finite_complete_resources_with_history holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved
  obtain ⟨arityBound, arityOutcome, arityRunning, _arityResources, strengthened⟩ :=
    run_finite_complete_resources_arity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved arity
  have oldAt := running arityBound
  have newAt := arityRunning historyBound
  have fuelSame : arityBound + historyBound = historyBound + arityBound := by omega
  rw [fuelSame] at newAt
  have outcomeSame : arityOutcome = outcome := newAt.symm.trans oldAt
  rw [outcomeSame] at strengthened
  have outputHeaps : ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
      ArityHeap output.caller.checked.native.machine.heap := by
    obtain ⟨_reached, _next, _final, _post, _bounded, _known, _arity, shape⟩ := strengthened
    cases outcome with
    | complete outputs reached saved =>
        intro output member
        exact (shape.2.2 output member).2
    | stopped outputs reason endpoint =>
        intro output member
        exact (shape.2 output member).2
  have historiesAt : ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
        (historyBound + arityBound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
        (SourcePruningEnumerationRestart.decision stop order metadata before) output := by
    intro extra output member
    simpa only [Nat.add_assoc] using histories (arityBound + extra) output member
  refine ⟨historyBound + arityBound, outcome, ?_, resources, historiesAt, strengthened, ?_⟩
  · intro extra
    simpa only [Nat.add_assoc] using running (arityBound + extra)
  · intro extra output member
    exact (historiesAt extra output member).with_arity_of_output_heap (outputHeaps output member)

end MicroCFTA.SourcePruningEnumerationRecursive
