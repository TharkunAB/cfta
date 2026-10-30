import MicroCFTA.SourcePruningEnumerationFiniteParkedResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteParkedResources
import MicroCFTA.SourcePruningEnumerationExecutionPaths
import MicroCFTA.SourcePruningEnumerationPathSelectedPrefix

/-!
# Internal resource and execution paths for a parked expansion

The smaller-depth execution premise is an internal induction hypothesis.
The same bound applies to the resource outcome and all actual execution paths.
The original-input theorem must derive the induction hypotheses.
-/

namespace MicroCFTA.SourcePruningEnumerationExecutionParkedBridge.Native
open SourcePruningEnumerationRecursive
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

open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationExecutionPathData (OutcomePaths NativeFailurePaths PreparedFailurePaths)
open SourcePruningEnumerationPathSelectedRaw (SelectedPrefixPaths)
open SourcePruningEnumerationExecutionPaths (ResumeNative ResumePrepared)
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound

/-- Retain the parked resource outcome and every literal recursive execution path. -/
theorem parked_finite_complete_resources_paths
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
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query))
    (P : EqualityTrie.Path → Prop)
    (paths : StatePaths P before.core)
    (projected : ProjectionPaths (SourcePruningEnumerationFiniteReservation.final (recursiveFuel + 1) seed ceiling).1 P)
    (pathsIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2))
        (nextMemos : Memos) (nextCache : Cached) (nextMetadata : Metadata Typing)
        (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextCache →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      suspendedBound nextCache.core ≤ nextCeiling →
      SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel nextSeed nextCeiling →
      StatePaths P nextCache.core →
      ProjectionPaths (SourcePruningEnumerationFiniteReservation.final recursiveFuel nextSeed nextCeiling).1 P →
      ∃ bound, ∀ extra,
        SourcePruningEnumerationExecutionPaths.Native P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ (bound : Nat) (outcome : Result),
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final (recursiveFuel + 1) seed ceiling) outcome ∧
      (∀ extra, ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) (recursiveFuel + 1) metadata caller memos.query before (some (.expand uv))) := by
  have selectedPaths := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
    holeKey fits admits graph templates stop order metadata
    (prefixFuel + 0) (prefixFuel + 0) (prefixFuel + 0)
    (prefixFuel + 0) (prefixFuel + 0) (prefixFuel + 0) uv caller before memos.query paths
  rw [(phase 0).1] at selectedPaths
  have checkedPaths : StatePaths P checked.core := selectedPaths.1

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
      rw [resume, observed]
    · intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      have actualPrefixPaths := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
        holeKey fits admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query paths
      rw [observed] at actualPrefixPaths
      refine ⟨paths, ?_, ?_⟩
      · rw [resume, observed]
        intro output member
        exact False.elim (List.not_mem_nil member)
      · dsimp only
        rw [observed]
        exact ⟨actualPrefixPaths, True.intro⟩
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
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
      selectionMembers selectionLength boundedMass reserved.first.2
    have growth := SourcePruningEnumerationFiniteReservation.first_le_final recursiveFuel seed ceiling
    have smallerProjected : ProjectionPaths
      (SourcePruningEnumerationFiniteReservation.final recursiveFuel parkedSeed parkedMass).1 P := by
      intro guard member
      exact projected guard (growth.2 member)
    obtain ⟨pathFuel, continuing⟩ := pathsIH inventory caller memos checked metadata parkedSeed parkedMass
      checkedPacket parkedFits parkedKnown selectionMembers selectionLength boundedMass reserved.first.2
      checkedPaths smallerProjected
    refine ⟨prefixFuel + resumeFuel + pathFuel, outcome, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      have observed := (phase (resumeFuel + pathFuel + extra)).1
      have prefixSame : prefixFuel + (resumeFuel + pathFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      rw [resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
        (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel metadata caller memos.query before uv
        checked.core checked.core checked metadata (SourcePruningEnumerationRestart.decision stop order metadata checked)
        observed, framed]
      have actual := running (prefixFuel + pathFuel + extra)
      have common : resumeFuel + (prefixFuel + pathFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [common] at actual
      exact actual
    · intro extra
      have observed := (phase (resumeFuel + pathFuel + extra)).1
      have prefixSame : prefixFuel + (resumeFuel + pathFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actualPrefixPaths := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
        holeKey fits admits graph templates stop order metadata
        (prefixFuel + resumeFuel + pathFuel + extra) (prefixFuel + resumeFuel + pathFuel + extra)
        (prefixFuel + resumeFuel + pathFuel + extra) (prefixFuel + resumeFuel + pathFuel + extra)
        (prefixFuel + resumeFuel + pathFuel + extra) (prefixFuel + resumeFuel + pathFuel + extra)
        uv caller before memos.query paths
      rw [observed] at actualPrefixPaths
      have nextExecution := continuing (prefixFuel + resumeFuel + extra)
      have pathWork : pathFuel + (prefixFuel + resumeFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [pathWork] at nextExecution
      have nextResume : ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel metadata caller memos.query checked
          (SourcePruningEnumerationRestart.decision stop order metadata checked) := nextExecution
      have nextOutcome : OutcomePaths P (NativeFailurePaths P)
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel metadata caller memos.query checked
            (SourcePruningEnumerationRestart.decision stop order metadata checked)) := by
        cases recursiveFuel with
        | zero => exact nextResume.2
        | succ fuel => exact nextResume.2.1
      refine ⟨paths, ?_, ?_⟩
      · rw [resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel metadata caller memos.query before uv
          checked.core checked.core checked metadata (SourcePruningEnumerationRestart.decision stop order metadata checked)
          observed, framed]
        exact nextOutcome
      · dsimp only
        rw [observed]
        refine ⟨actualPrefixPaths, ?_⟩
        dsimp only
        rw [framed]
        exact nextResume

end MicroCFTA.SourcePruningEnumerationExecutionParkedBridge.Native

namespace MicroCFTA.SourcePruningEnumerationExecutionParkedBridge.Prepared
open SourcePruningEnumerationPreparedRecursive
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

open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationExecutionPathData (OutcomePaths NativeFailurePaths PreparedFailurePaths)
open SourcePruningEnumerationPathSelectedRaw (SelectedPrefixPaths)
open SourcePruningEnumerationExecutionPaths (ResumeNative ResumePrepared)
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound

/-- Retain the parked resource outcome and every literal recursive execution path. -/
theorem parked_finite_complete_resources_paths
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
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query))
    (P : EqualityTrie.Path → Prop)
    (paths : StatePaths P before.core)
    (projected : ProjectionPaths (SourcePruningEnumerationPreparedReservation.final (recursiveFuel + 1) seed ceiling).1 P)
    (pathsIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2))
        (nextMemos : Memos) (nextCache : Cached) (nextMetadata : Metadata Typing)
        (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextCache →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      suspendedBound nextCache.core ≤ nextCeiling →
      SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel nextSeed nextCeiling →
      StatePaths P nextCache.core →
      ProjectionPaths (SourcePruningEnumerationPreparedReservation.final recursiveFuel nextSeed nextCeiling).1 P →
      ∃ bound, ∀ extra,
        SourcePruningEnumerationExecutionPaths.Prepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ (bound : Nat) (outcome : Result),
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final (recursiveFuel + 1) seed ceiling) outcome ∧
      (∀ extra, ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) (recursiveFuel + 1) metadata caller memos.query before (some (.expand uv))) := by
  have selectedPaths := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
    holeKey fits admits graph templates stop order metadata
    (prefixFuel + 0) (prefixFuel + 0) (prefixFuel + 0)
    (prefixFuel + 0) (prefixFuel + 0) (prefixFuel + 0) uv caller before memos.query paths
  rw [(phase 0).1] at selectedPaths
  have checkedPaths : StatePaths P checked.core := selectedPaths.1

  have valid := (phase 0).2
  rw [(phase 0).1] at valid
  have checkedPacket : Packet formulas solver inventory caller memos metadata checked :=
    SourcePruningEnumerationRecursive.prefix_packet holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
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
    have growth := SourcePruningEnumerationPreparedReservation.final_ge (recursiveFuel + 1) seed ceiling
    refine ⟨prefixFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [resume, observed]
    · intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      have actualPrefixPaths := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
        holeKey fits admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query paths
      rw [observed] at actualPrefixPaths
      refine ⟨paths, ?_, ?_⟩
      · rw [resume, observed]
        intro output member
        exact False.elim (List.not_mem_nil member)
      · dsimp only
        rw [observed]
        exact ⟨actualPrefixPaths, True.intro⟩
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
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
      selectionMembers selectionLength boundedMass reserved.first.2
    have growth := SourcePruningEnumerationPreparedReservation.first_le_final recursiveFuel seed ceiling
    have smallerProjected : ProjectionPaths
      (SourcePruningEnumerationPreparedReservation.final recursiveFuel parkedSeed parkedMass).1 P := by
      intro guard member
      exact projected guard (growth.2 member)
    obtain ⟨pathFuel, continuing⟩ := pathsIH inventory caller memos checked metadata parkedSeed parkedMass
      checkedPacket parkedFits parkedKnown selectionMembers selectionLength boundedMass reserved.first.2
      checkedPaths smallerProjected
    refine ⟨prefixFuel + resumeFuel + pathFuel, outcome, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      have observed := (phase (resumeFuel + pathFuel + extra)).1
      have prefixSame : prefixFuel + (resumeFuel + pathFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      rw [resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
        (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel uv metadata metadata caller memos.query before
        checked checked.core checked.core (SourcePruningEnumerationRestart.decision stop order metadata checked)
        observed, framed]
      have actual := running (prefixFuel + pathFuel + extra)
      have common : resumeFuel + (prefixFuel + pathFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [common] at actual
      exact actual
    · intro extra
      have observed := (phase (resumeFuel + pathFuel + extra)).1
      have prefixSame : prefixFuel + (resumeFuel + pathFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [prefixSame, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actualPrefixPaths := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
        holeKey fits admits graph templates stop order metadata
        (prefixFuel + resumeFuel + pathFuel + extra) (prefixFuel + resumeFuel + pathFuel + extra)
        (prefixFuel + resumeFuel + pathFuel + extra) (prefixFuel + resumeFuel + pathFuel + extra)
        (prefixFuel + resumeFuel + pathFuel + extra) (prefixFuel + resumeFuel + pathFuel + extra)
        uv caller before memos.query paths
      rw [observed] at actualPrefixPaths
      have nextExecution := continuing (prefixFuel + resumeFuel + extra)
      have pathWork : pathFuel + (prefixFuel + resumeFuel + extra) =
          prefixFuel + resumeFuel + pathFuel + extra := by omega
      rw [pathWork] at nextExecution
      have nextResume : ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel metadata caller memos.query checked
          (SourcePruningEnumerationRestart.decision stop order metadata checked) := nextExecution
      have nextOutcome : OutcomePaths P (PreparedFailurePaths P)
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel metadata caller memos.query checked
            (SourcePruningEnumerationRestart.decision stop order metadata checked)) := by
        cases recursiveFuel with
        | zero => exact nextResume.2
        | succ fuel => exact nextResume.2.1
      refine ⟨paths, ?_, ?_⟩
      · rw [resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + resumeFuel + pathFuel + extra) recursiveFuel uv metadata metadata caller memos.query before
          checked checked.core checked.core (SourcePruningEnumerationRestart.decision stop order metadata checked)
          observed, framed]
        exact nextOutcome
      · dsimp only
        rw [observed]
        refine ⟨actualPrefixPaths, ?_⟩
        dsimp only
        rw [framed]
        exact nextResume

end MicroCFTA.SourcePruningEnumerationExecutionParkedBridge.Prepared

