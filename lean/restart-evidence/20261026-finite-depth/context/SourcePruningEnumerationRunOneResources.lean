import MicroCFTA.SourcePruningEnumerationOneExpansionResources
import MicroCFTA.SourcePruningEnumerationZeroOutcomeResources

/-!
# The actual recursive driver at depth one

The current packet and one original reservation supply a common work bound.
The result retains its actual endpoint and each emitted output packet.
The theorem includes the initial stop, done and stuck decisions.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
local notation "narrowSeed" => SourcePruningEnumerationExpansionAdmission.narrowSeed
local notation "forecastCount" => SourcePruningEnumerationExpansionAdmission.count
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original current inputs derive a stable actual depth-one driver result at every larger work fuel. -/
theorem run_one_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : Reserved bits (narrowSeed seed) (forecastCount seed before.core)) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 1
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (reservationAdvance (narrowSeed seed) (forecastCount seed before.core)) outcome := by
  by_cases expansion : ∃ uv,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)
  · obtain ⟨uv, chosen⟩ := expansion
    obtain ⟨bound, outcome, running, resources⟩ := selected_one_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
      caller memos before metadata uv seed packet bounded known selectionMembers selectionLength reserved chosen
    exact ⟨bound, outcome, fun extra => by simpa only [run, chosen] using running extra, resources⟩
  · obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
      caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
      seed packet bounded known
    have numeric := (SourceCurrentConstrainedCapEditForecast.headProfile_ge seed.2).trans
      (SourcePruningEnumerationIncomingReservation.advance_profile_ge
        (seed.1, SourceCurrentConstrainedCapEditForecast.headProfile seed.2) (forecastCount seed before.core))
    have alphabet : seed.1 ⊆
        (reservationAdvance (narrowSeed seed) (forecastCount seed before.core)).1 :=
      SourcePruningEnumerationIncomingReservation.advance_alphabet_ge
        (seed.1, SourceCurrentConstrainedCapEditForecast.headProfile seed.2) (forecastCount seed before.core)
    refine ⟨0, outcome, ?_, resources.mono numeric alphabet⟩
    intro extra
    have zero := running extra
    unfold run
    cases selected : SourcePruningEnumerationRestart.decision stop order metadata before with
    | none => simpa only [selected, resume] using zero
    | some next =>
        cases next with
        | done => simpa only [selected, resume] using zero
        | stuck => simpa only [selected, resume] using zero
        | expand uv => exact False.elim (expansion ⟨uv, selected⟩)

end MicroCFTA.SourcePruningEnumerationRecursive
