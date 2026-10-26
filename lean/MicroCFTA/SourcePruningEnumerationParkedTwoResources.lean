import MicroCFTA.SourcePruningEnumerationPrefixMass
import MicroCFTA.SourcePruningEnumerationTwoExpansionForecast
import MicroCFTA.SourcePruningEnumerationRunOneResources

/-!
# A parked first expansion followed by the actual depth-one driver

The original envelope reserves the remaining recursive step. The literal
prefix execution derives the checked cache's mass bound. The caller and
full memos then pass to the actual depth-one restart.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
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
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- The original reservation derives the actual parked depth-two outcome at one common work bound. -/
theorem parked_two_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (prefixFuel uv : Nat) (checked : Cached) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : SourcePruningEnumerationTwoExpansionForecast.Reserved bits seed before.core)
    (phase : ∀ extra,
      SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query =
        .parked checked.core (some checked)
          (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core))) ∧
      SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + extra) uv caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query)) :
    ∃ (bound : Nat) (outcome : Result),
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 2
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationTwoExpansionForecast.final seed before.core) outcome := by
  have valid := (phase 0).2
  rw [(phase 0).1] at valid
  have checkedPacket : Packet formulas solver inventory caller memos metadata checked :=
    prefix_packet holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid
  have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (prefixFuel + 0) uv caller memos before packet _ valid (phase 0).1
  have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
    cases checked
    rfl
  by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
    have growth := SourcePruningEnumerationTwoExpansionForecast.final_ge seed before.core
    refine ⟨prefixFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2⟩
    intro extra
    have observed := (phase extra).1
    rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
    rw [resume, observed]
  · let parkedSeed := SourcePruningEnumerationRecursiveReservation.afterHead
      (SourcePruningEnumerationTwoExpansionForecast.start seed)
      (SourcePruningEnumerationPrefixAdmission.suspendedBound before.core)
    have initialGrowth := SourcePruningEnumerationTwoExpansionForecast.parked_input_padding seed before.core
    have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono initialGrowth.1
    have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
      fun key edge resident => initialGrowth.2 (known key edge resident)
    have parkedReserved := reserved.parked checked.core checkedMass
    obtain ⟨resumeFuel, outcome, running, resources⟩ := run_one_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory caller memos
      checked metadata parkedSeed checkedPacket parkedFits parkedKnown selectionMembers selectionLength parkedReserved
    have growth := SourcePruningEnumerationTwoExpansionForecast.parked_final_padding seed before.core checked.core checkedMass
    refine ⟨prefixFuel + resumeFuel, outcome, ?_, resources.mono growth.1 growth.2⟩
    intro extra
    have observed := (phase (resumeFuel + extra)).1
    have prefixSame : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
    rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
    rw [resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
      (prefixFuel + resumeFuel + extra) 1 metadata caller memos.query before uv checked.core checked.core checked metadata
      (SourcePruningEnumerationRestart.decision stop order metadata checked) observed, framed]
    have actual := running (prefixFuel + extra)
    have common : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
    rw [common] at actual
    exact actual

end MicroCFTA.SourcePruningEnumerationRecursive
