import MicroCFTA.SourceFlatPruningFiniteContract
import MicroCFTA.SourceFlatPruningRecursivePrefixShape
import MicroCFTA.SourcePruningEnumerationFiniteParkedResources

/-!
# Actual flat parked recursion under an original reservation

One original prefix bound applies to every related flat cache.
The returned parked cache supplies the same smaller-depth induction input.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet OutcomeResources prefix_packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
local notation "OldResult" => SourcePruningEnumerationNativeContinuations.HookResult
  (SourcePruningEnumerationRecursive.Output (bits + 2) Typing)
  (SourcePruningEnumerationRecursive.Failure (bits + 2) Typing) (bits + 2)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An original parked prefix and smaller-depth contract derive every actual flat continuation. -/
theorem parked_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (prefixFuel uv : Nat) (checked : Cached) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
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
    ∃ (bound : Nat) (outcome : OldResult),
      (∀ extra, SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) (recursiveFuel + 1) metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final (recursiveFuel + 1) seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) (recursiveFuel + 1) metadata caller memos.query flat (some (.expand uv)) = flatOutcome ∧
          ResultRelated flatOutcome outcome := by
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
    have growth := SourcePruningEnumerationFiniteReservation.final_ge (recursiveFuel + 1) seed ceiling
    refine ⟨prefixFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [SourcePruningEnumerationRecursive.resume, observed]
    · intro flat related extra
      have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
        holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
        (prefixFuel + extra) uv caller before flat memos related (phase extra).2
      rw [(phase extra).1, SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at replay
      obtain ⟨flatChecked, flatAfter, flatRaw, observed, _caches, rows⟩ :=
        SourceFlatPruningRecursivePrefixShape.parked _ checked.core checked [] replay
      obtain rfl := SourceFlatPruningRecursivePrefixShape.rows_nil rows
      refine ⟨.complete [] caller memos.query, ?_, .nil, rfl, rfl⟩
      rw [resume, observed]
  · let start := SourcePruningEnumerationExpansionAdmission.narrowSeed seed
    let parkedSeed := SourcePruningEnumerationRecursiveReservation.afterHead start ceiling
    let parkedMass := SourcePruningEnumerationRecursiveReservation.massCeil start ceiling ceiling
    have narrowGrowth := SourcePruningEnumerationFiniteReservation.narrowSeed_ge seed
    have headGrowth := SourcePruningEnumerationRecursiveReservation.afterHead_ge start ceiling
    have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
    have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
      fun key edge resident => headGrowth.2 (narrowGrowth.2 (known key edge resident))
    have boundedMass : SourcePruningEnumerationPrefixAdmission.suspendedBound checked.core ≤ parkedMass :=
      Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
    obtain ⟨resumeFuel, outcome, running, resources, flatRunning⟩ := recursive
      inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
      selectionMembers selectionLength boundedMass reserved.first.2
    have growth := SourcePruningEnumerationFiniteReservation.first_le_final recursiveFuel seed ceiling
    refine ⟨prefixFuel + resumeFuel, outcome, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      have observed := (phase (resumeFuel + extra)).1
      have prefixSame : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      rw [SourcePruningEnumerationRecursive.resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
        (prefixFuel + resumeFuel + extra) recursiveFuel metadata caller memos.query before uv checked.core checked.core checked metadata
        (SourcePruningEnumerationRestart.decision stop order metadata checked) observed, framed]
      have actual := running (prefixFuel + extra)
      have common : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common] at actual
      exact actual
    · intro flat related extra
      let w := prefixFuel + resumeFuel + extra
      have prefixSame : prefixFuel + (resumeFuel + extra) = w := by dsimp [w]; omega
      have actualPhase := phase (resumeFuel + extra)
      rw [prefixSame] at actualPhase
      have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
        holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
        w uv caller before flat memos related actualPhase.2
      rw [actualPhase.1, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at replay
      obtain ⟨flatChecked, flatAfter, flatRaw, observed, caches, rows⟩ :=
        SourceFlatPruningRecursivePrefixShape.parked _ checked.core checked _ replay
      obtain ⟨flatCore, rawSame, states⟩ := SourceFlatPruningRecursivePrefixShape.rows_singleton rows
      rw [rawSame] at observed
      have restored : EnumerationFlatCached.Related (EnumerationFlatCached.frame flatCore flatAfter) checked := by
        simpa only [framed] using EnumerationFlatCached.frame_related caches states
      obtain ⟨flatOutcome, actual, relatedOutcome⟩ :=
        flatRunning (EnumerationFlatCached.frame flatCore flatAfter) restored (prefixFuel + extra)
      have common : resumeFuel + (prefixFuel + extra) = w := by dsimp [w]; omega
      rw [common] at actual
      refine ⟨flatOutcome, ?_, relatedOutcome⟩
      change resume holeKey fits admits graph templates checkEmpty edgesOf stop order w (recursiveFuel + 1)
        metadata caller memos.query flat (some (.expand uv)) = flatOutcome
      rw [resume, observed]
      unfold run at actual
      rw [SourceFlatPruningRestart.decision_related restored stop order metadata] at actual
      exact actual

end MicroCFTA.SourceFlatPruningRecursive
