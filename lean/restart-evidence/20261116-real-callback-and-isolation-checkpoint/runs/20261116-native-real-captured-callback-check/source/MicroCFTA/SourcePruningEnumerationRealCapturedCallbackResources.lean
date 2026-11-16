import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationSharedPreparedCallbackResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningCallbackExact

import MicroCFTA.SourcePruningEnumerationRealWorkerCallbackResources

set_option autoImplicit false
namespace MicroCFTA.SourcePruningEnumerationRealCapturedCallbackResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame EnumerationDriver
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure OutputResources OutcomeResources emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (runEagerWithNarrow runWithNarrow resumeWithNarrow)
open SourcePruningEnumerationSharedEagerReservation (eagerFinal eagerReserved eagerFinal_ge)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
/-- A completed real callback restores its captured input cache at the original budget. -/
theorem completed_real_callback_captured_packet_at_original_budget
    [DecidableEq Symbol] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveDepth : Nat)
    (workerIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2)) (nextMemos : Memos)
        (nextBefore : Cached) (nextMetadata : Metadata Typing) (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextBefore →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      SourcePruningEnumerationPrefixAdmission.suspendedBound nextBefore.core ≤ nextCeiling →
      eagerReserved bits recursiveDepth nextSeed nextCeiling →
      ∀ sameWorkFuel,
        let outcome := runEagerWithNarrow (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order sameWorkFuel recursiveDepth
          nextMetadata nextCaller nextMemos.query nextBefore
        (∀ output ∈ emitted outcome,
          OutputResources formulas solver nextCaller (eagerFinal recursiveDepth nextSeed nextCeiling) output) ∧
        match outcome with
        | .complete _ _ _ => OutcomeResources formulas solver nextCaller
            (eagerFinal recursiveDepth nextSeed nextCeiling) outcome
        | .stopped _ _ _ => True)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (before : Cached) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling) (workFuel : Nat)
    (outputs : List (Output (bits + 2) Typing))
    (reached : Caller (bits + 2)) (saved : SourceEndpointMemo.Memos)
    (observed : SourcePruningEnumerationSharedPreparedRecursive.continueWith
      (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
      graph templates stop order workFuel metadata uv fragment caller memos.query before =
        .complete outputs reached saved) :
    ∃ (next : Inventory) (final : Memos),
      Post formulas solver next caller reached final ∧ final.query = saved ∧
      Packet formulas solver next reached final metadata before ∧
      Fits (eagerFinal recursiveDepth seed ceiling).2 reached.checked ∧
      Heap (fun guard => guard ∈ (eagerFinal recursiveDepth seed ceiling).1)
        reached.checked.native.machine.heap ∧
      ∀ output ∈ outputs,
        OutputResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) output
 := by
  have resources :=
    SourcePruningEnumerationRealWorkerCallbackResources.real_callback_resources_of_depth_induction
      holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveDepth workerIH inventory caller memos before metadata uv fragment
      seed ceiling packet allocated bounded known selectionMembers selectionLength mass reserved workFuel
  rw [observed] at resources
  exact SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet
    formulas solver inventory caller memos metadata before (eagerFinal recursiveDepth seed ceiling)
    outputs reached saved packet resources.2

end MicroCFTA.SourcePruningEnumerationRealCapturedCallbackResources

#check MicroCFTA.SourcePruningEnumerationRealCapturedCallbackResources.completed_real_callback_captured_packet_at_original_budget
#print axioms MicroCFTA.SourcePruningEnumerationRealCapturedCallbackResources.completed_real_callback_captured_packet_at_original_budget
