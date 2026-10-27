import MicroCFTA.SourceFlatPruningRecursiveExpansionResources
import MicroCFTA.SourcePruningEnumerationZeroOutcomeResources

/-!
# Actual flat and original drivers at positive finite depth

The current packet and one original reservation supply a common work bound.
The result retains its actual endpoint and each emitted output packet.
The theorem includes the initial stop, done and stuck decisions.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet OutcomeResources resume_zero_outcome_resources)
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

/-- Original current inputs derive a stable actual positive-depth driver result at every larger work fuel. -/
theorem run_finite_succ_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits (recursiveFuel + 1) seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final (recursiveFuel + 1) seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          run holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) (recursiveFuel + 1) metadata caller memos.query flat = flatOutcome ∧
          ResultRelated flatOutcome outcome := by
  by_cases expansion : ∃ uv,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)
  · obtain ⟨uv, chosen⟩ := expansion
    obtain ⟨bound, outcome, running, resources, flatRunning⟩ := selected_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel recursive inventory
      caller memos before metadata uv seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved chosen
    refine ⟨bound, outcome, fun extra => by simpa only [SourcePruningEnumerationRecursive.run, chosen] using running extra,
      resources, ?_⟩
    intro flat related extra
    obtain ⟨flatOutcome, actual, corresponds⟩ := flatRunning flat related extra
    refine ⟨flatOutcome, ?_, corresponds⟩
    unfold run
    rw [SourceFlatPruningRestart.decision_related related stop order metadata, chosen]
    exact actual
  · obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
      caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
      seed packet bounded known
    have growth := SourcePruningEnumerationFiniteReservation.final_ge (recursiveFuel + 1) seed ceiling
    have originalRunning : ∀ extra,
        SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf stop order
          (0 + extra) (recursiveFuel + 1) metadata caller memos.query before = outcome := by
      intro extra
      have zero := running extra
      unfold SourcePruningEnumerationRecursive.run
      cases selected : SourcePruningEnumerationRestart.decision stop order metadata before with
      | none => simpa only [selected, SourcePruningEnumerationRecursive.resume, Nat.zero_add] using zero
      | some next =>
          cases next with
          | done => simpa only [selected, SourcePruningEnumerationRecursive.resume, Nat.zero_add] using zero
          | stuck => simpa only [selected, SourcePruningEnumerationRecursive.resume, Nat.zero_add] using zero
          | expand uv => exact False.elim (expansion ⟨uv, selected⟩)
    refine ⟨0, outcome, originalRunning, resources.mono growth.1 growth.2, ?_⟩
    intro flat related extra
    refine ⟨_, rfl, ?_⟩
    rw [← originalRunning extra]
    unfold run SourcePruningEnumerationRecursive.run
    rw [SourceFlatPruningRestart.decision_related related stop order metadata]
    apply resume_nonexpanding_related holeKey fits admits graph templates checkEmpty edgesOf stop order
      (0 + extra) metadata caller memos.query flat before related (recursiveFuel + 1)
      (SourcePruningEnumerationRestart.decision stop order metadata before)
    intro uv chosen
    exact expansion ⟨uv, chosen⟩

end MicroCFTA.SourceFlatPruningRecursive
