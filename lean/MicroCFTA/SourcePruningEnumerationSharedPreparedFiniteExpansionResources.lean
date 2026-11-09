import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteDispatchResources
import MicroCFTA.SourcePruningEnumerationPrefixMass
import MicroCFTA.SourcePruningEnumerationSelectedPreparationCurrent

/-!
# Actual prepared shared expansion at a positive finite depth

The unchanged prefix supplies its actual packet and selected incoming
condition. One common preparation then dispatches the current shared
ordinary or opaque branch. Both branches include their actual callbacks.
The smaller-depth hypothesis quantifies current packets and resources.
-/

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open InternedProbeProvenance SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSelectedStep (runPrefix)
open SourcePruningEnumerationSharedRecursive (checkpoint_resources CurrentPrefixFacts)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "Forecast" => SourcePruningEnumerationSharedPreparedReservation.final
local notation "stage" => SourcePruningEnumerationSharedPreparedReservation.stage
local notation "RowResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
attribute [local irreducible] SourcePruningEnumerationSharedPreparedReservation.step
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Symbol] [DecidableEq Node]

/-- Current inputs and the smaller-depth hypothesis derive the literal shared positive expansion. -/
theorem expansion_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : mass before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (Forecast (recursiveFuel + 1) seed ceiling) outcome := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  have finalGrowth := SourcePruningEnumerationSharedPreparedReservation.final_ge (recursiveFuel + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
  have stageGrowth := SourcePruningEnumerationSharedPreparedReservation.stage_ge
    recursiveFuel start ceiling ceiling (SourcePruningEnumerationSharedPreparedReservation.rows seed)
  obtain ⟨currentFuel, phases⟩ := checkpoint_resources holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  obtain ⟨legacyFuel, legacyComplete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet
  let prefixFuel := currentFuel + legacyFuel
  have shift (extra : Nat) : currentFuel + (legacyFuel + extra) = prefixFuel + extra := by
    dsimp only [prefixFuel]
    omega
  have legacy (extra : Nat) : SourcePruningEnumerationSelectedStep.PrefixValid
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + extra) uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query) := by
    have valid := legacyComplete (currentFuel + extra) uv chosen
    have common : legacyFuel + (currentFuel + extra) = prefixFuel + extra := by
      dsimp only [prefixFuel]
      omega
    simpa only [common] using valid
  rcases phases with ⟨checked, originalPhase⟩ | ⟨checked, heap, originalPhase⟩ |
    ⟨checked, phaseValue, heap, after, _nonempty, originalPhase⟩
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have valid := legacy 0
    rw [(phase 0).1] at valid
    have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet _ valid (phase 0).1
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
    · have certificate : OutcomeResources (Typing := Typing) formulas solver caller seed
          (.complete [] caller memos.query) := by
        refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_, certificate.mono finalGrowth.1 finalGrowth.2⟩
      intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [resume, observed]
    · let parkedSeed := SourcePruningEnumerationSharedPreparedReservation.afterHead start ceiling
      let parkedMass := SourcePruningEnumerationRecursiveReservation.massCeil start ceiling ceiling
      have headGrowth := SourcePruningEnumerationSharedPreparedReservation.afterHead_ge start ceiling
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : mass checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound reserved.first.2
      have growth := SourcePruningEnumerationSharedPreparedReservation.first_le_final recursiveFuel seed ceiling
      have callbackResources : OutcomeResources formulas solver caller
          (SourcePruningEnumerationSharedPreparedReservation.step recursiveFuel start ceiling ceiling) outcome := by
        simpa only [SourcePruningEnumerationSharedPreparedReservation.step, parkedSeed, parkedMass] using resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, callbackResources.mono growth.1 growth.2⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [resume, observed]
      dsimp only
      rw [framed]
      exact actual
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
    have certificate : OutcomeResources (Typing := Typing) formulas solver caller start
        (.complete [] reached memos.query) := by
      refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
        current.2.2, rfl, query.symm, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
    · intro extra
      rw [resume, (phase extra).1]
    · have padded := certificate.mono stageGrowth.1 stageGrowth.2
      simpa only [SourcePruningEnumerationSharedPreparedReservation.final_succ] using padded
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨_action, prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      CurrentPrefixFacts.right_packet current.1
    have valid := legacy 0
    rw [prefixAt] at valid
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ valid
    obtain ⟨handle, scs, _value, _oldMemos, _oldPost, _oldQuery, _oldPacket, ready, stored,
      _decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      _oldFits, _oldKnown⟩ := admission
    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
        reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : mass after.core ≤ ceiling := Nat.le_trans
      (SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt)
      initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    obtain ⟨scanFuel, _observation, result, scanRun, certificate⟩ := prepared_dispatch_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed
      formulas solver recursive inventory reached middleMemos after uv handle scs
      middlePacket ready stored incoming middleFits middleKnown selectionMembers selectionLength
      ceiling currentMass inheritedLength reserved
    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost⟩
    intro extra
    obtain ⟨currentAction, currentPrefix, _current⟩ := phase (scanFuel + extra)
    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [common] at currentPrefix
    have actual := scanRun (prefixFuel + extra)
    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [scanCommon, middleQuery] at actual
    rw [resume, currentPrefix]
    dsimp only
    rw [actual]

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
