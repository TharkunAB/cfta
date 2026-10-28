import MicroCFTA.SourcePruningEnumerationPrefixMass
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationRecursivePrefix
import MicroCFTA.SourcePruningEnumerationPreparedResumeExecution

/-!
# Actual admitted histories through a parked first expansion

The prepared envelope reserves the remaining recursive steps. The literal
prefix execution derives the checked cache's mass bound. The caller and
full memos then pass to the actual smaller-depth restart.
Each actual output retains its original admitted parked transition.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
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

/-- The original reservation derives the actual parked finite-depth outcome at one common work bound. -/
theorem parked_finite_complete_resources_with_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (prefixFuel uv : Nat) (checked : Cached) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
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
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final (recursiveFuel + 1) seed ceiling) outcome ∧
      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) (recursiveFuel + 1) inventory caller memos metadata before seed ceiling
          (some (.expand uv)) output := by
  have valid := (phase 0).2
  rw [(phase 0).1] at valid
  have checkedPacket : Packet formulas solver inventory caller memos metadata checked :=
    SourcePruningEnumerationRecursive.prefix_packet holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid
  have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (prefixFuel + 0) uv caller memos before packet _ valid (phase 0).1
  have admission : HistoryAdmission formulas solver inventory caller memos metadata before
      (recursiveFuel + 1) seed ceiling := ⟨packet, bounded, known, initialMass, reserved⟩
  have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
    cases checked
    rfl
  by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
    have growth := SourcePruningEnumerationPreparedReservation.final_ge (recursiveFuel + 1) seed ceiling
    refine ⟨prefixFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [resume, observed]
    · intro extra output member
      cases member
  · let start := SourcePruningEnumerationPreparedReservation.preparedSeed seed
    let parkedSeed := SourcePruningEnumerationRecursiveReservation.afterHead start ceiling
    let parkedMass := SourcePruningEnumerationRecursiveReservation.massCeil start ceiling ceiling
    have narrowGrowth := SourcePruningEnumerationPreparedReservation.preparedSeed_ge seed
    have headGrowth := SourcePruningEnumerationRecursiveReservation.afterHead_ge start ceiling
    have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
    have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
      fun key edge resident => headGrowth.2 (narrowGrowth.2 (known key edge resident))
    have boundedMass : SourcePruningEnumerationPrefixAdmission.suspendedBound checked.core ≤ parkedMass :=
      Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
    obtain ⟨resumeFuel, outcome, running, resources, histories⟩ := recursive
      inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
      selectionMembers selectionLength boundedMass reserved.first.2
    have growth := SourcePruningEnumerationPreparedReservation.first_le_final recursiveFuel seed ceiling
    refine ⟨prefixFuel + resumeFuel, outcome, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      have observed := (phase (resumeFuel + extra)).1
      have prefixSame : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      rw [resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
        (prefixFuel + resumeFuel + extra) recursiveFuel uv metadata metadata caller memos.query before checked checked.core checked.core
        (SourcePruningEnumerationRestart.decision stop order metadata checked) observed, framed]
      have actual := running (prefixFuel + extra)
      have common : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common] at actual
      exact actual
    · intro extra output member
      have observed := (phase (resumeFuel + extra)).1
      have prefixSame : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have validAt : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
          checkEmpty edgesOf stop order metadata formulas solver inventory (prefixFuel + resumeFuel + extra)
          uv caller before memos
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (prefixFuel + resumeFuel + extra) (prefixFuel + resumeFuel + extra) (prefixFuel + resumeFuel + extra)
            (prefixFuel + resumeFuel + extra) (prefixFuel + resumeFuel + extra) (prefixFuel + resumeFuel + extra)
            uv caller before memos.query) := by
        simpa only [Nat.add_assoc] using (phase (resumeFuel + extra)).2
      have actualHistory := histories (prefixFuel + extra) output member
      have common : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common] at actualHistory
      have tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (prefixFuel + resumeFuel + extra) recursiveFuel inventory caller memos metadata
          (EnumerationExpandableIndex.frame checked.core checked) parkedSeed parkedMass
          (SourcePruningEnumerationRestart.decision stop order metadata checked) output := by
        rw [framed]
        exact actualHistory
      exact .parked admission validAt observed tail

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
