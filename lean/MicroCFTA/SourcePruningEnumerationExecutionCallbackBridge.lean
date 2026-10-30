import MicroCFTA.SourcePruningEnumerationFiniteCallbackResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteCallbackResources
import MicroCFTA.SourcePruningEnumerationPathRecordingValues

/-!
# Actual callback resources and the smaller execution-path induction

This module contains internal induction helpers.
The original-input theorem must discharge both induction premises.
-/

namespace MicroCFTA.SourcePruningEnumerationExecutionCallbackBridge.Native
open SourcePruningEnumerationRecursive
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)


/-- Keep every callback resource clause and add the actual recursive input paths. -/
theorem callback_finite_complete_resources_with_execution_ih
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop)
    (paths : StatePaths P before.core)
    (projected : ProjectionPaths
      (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling).1 P)
    (Paths : Nat → Metadata Typing → Caller (bits + 2) → Queries → Cached → Prop)
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
        Paths (bound + extra) nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      StatePaths P (EnumerationExpandableIndex.frame after before).core ∧
      (∀ extra, result.1 = false → Paths (fuel + extra) result.2 caller memos.query
        (EnumerationExpandableIndex.frame after before)) := by
  obtain ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing,
      callback, running, resources⟩ :=
    SourcePruningEnumerationRecursive.callback_finite_complete_resources
      holeKey fits admits formulas solver inventory graph templates metadata uv fragment caller memos before
      checkEmpty edgesOf stop order recursiveFuel recursive seed ceiling packet allocated bounded known
      selectionMembers selectionLength mass reserved
  have afterPaths : StatePaths P after :=
    SourcePruningEnumerationPathRecordingValues.recordTypes_paths graph templates (fuel + 0)
      metadata uv (.inl fragment) before.core after result paths (callback 0).1
  have framedPaths : StatePaths P (EnumerationExpandableIndex.frame after before).core := afterPaths
  by_cases continued : result.1 = false
  · have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨pathFuel, pathRunning⟩ := pathsIH inventory caller memos
      (EnumerationExpandableIndex.frame after before) result.2 seed ceiling returned bounded known
      selectionMembers selectionLength massAfter reserved framedPaths projected
    refine ⟨fuel + pathFuel, result, after, outcome, returned, stable, frame, types, holes, typing,
      ?_, ?_, resources, framedPaths, ?_⟩
    · intro extra
      simpa only [Nat.add_assoc] using callback (pathFuel + extra)
    · intro extra
      simpa only [Nat.add_assoc] using running (pathFuel + extra)
    · intro extra _actualFalse
      have actual := pathRunning (fuel + extra)
      have same : pathFuel + (fuel + extra) = fuel + pathFuel + extra := by omega
      rw [same] at actual
      exact actual
  · refine ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing,
      callback, running, resources, framedPaths, ?_⟩
    intro _extra impossible
    exact False.elim (continued impossible)

end MicroCFTA.SourcePruningEnumerationExecutionCallbackBridge.Native

namespace MicroCFTA.SourcePruningEnumerationExecutionCallbackBridge.Prepared
open SourcePruningEnumerationPreparedRecursive
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)


/-- Keep every callback resource clause and add the actual recursive input paths. -/
theorem callback_finite_complete_resources_with_execution_ih
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (P : EqualityTrie.Path → Prop)
    (paths : StatePaths P before.core)
    (projected : ProjectionPaths
      (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling).1 P)
    (Paths : Nat → Metadata Typing → Caller (bits + 2) → Queries → Cached → Prop)
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
        Paths (bound + extra) nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      StatePaths P (EnumerationExpandableIndex.frame after before).core ∧
      (∀ extra, result.1 = false → Paths (fuel + extra) result.2 caller memos.query
        (EnumerationExpandableIndex.frame after before)) := by
  obtain ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing,
      callback, running, resources⟩ :=
    SourcePruningEnumerationPreparedRecursive.callback_finite_complete_resources
      holeKey fits admits formulas solver inventory graph templates metadata uv fragment caller memos before
      checkEmpty edgesOf stop order recursiveFuel recursive seed ceiling packet allocated bounded known
      selectionMembers selectionLength mass reserved
  have afterPaths : StatePaths P after :=
    SourcePruningEnumerationPathRecordingValues.recordTypes_paths graph templates (fuel + 0)
      metadata uv (.inl fragment) before.core after result paths (callback 0).1
  have framedPaths : StatePaths P (EnumerationExpandableIndex.frame after before).core := afterPaths
  by_cases continued : result.1 = false
  · have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨pathFuel, pathRunning⟩ := pathsIH inventory caller memos
      (EnumerationExpandableIndex.frame after before) result.2 seed ceiling returned bounded known
      selectionMembers selectionLength massAfter reserved framedPaths projected
    refine ⟨fuel + pathFuel, result, after, outcome, returned, stable, frame, types, holes, typing,
      ?_, ?_, resources, framedPaths, ?_⟩
    · intro extra
      simpa only [Nat.add_assoc] using callback (pathFuel + extra)
    · intro extra
      simpa only [Nat.add_assoc] using running (pathFuel + extra)
    · intro extra _actualFalse
      have actual := pathRunning (fuel + extra)
      have same : pathFuel + (fuel + extra) = fuel + pathFuel + extra := by omega
      rw [same] at actual
      exact actual
  · refine ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing,
      callback, running, resources, framedPaths, ?_⟩
    intro _extra impossible
    exact False.elim (continued impossible)

end MicroCFTA.SourcePruningEnumerationExecutionCallbackBridge.Prepared
