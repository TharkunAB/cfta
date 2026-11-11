import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
import MicroCFTA.SourcePruningEnumerationPrefixProperHistory

/-!
# Proper storage in the actual current shared prefix packet

The current resource packet and the proper-state proof use the same prefix.
Both sufficient bounds come from the same initial inputs.
The proof retains no ordinary continuation from the validity receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationProgress InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSelectedStep (runPrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Current inputs derive resources and proper storage at the same actual prefix cache. -/
theorem prefix_complete_resources_proper
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (proper : ProperState before.core)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        selected caller before memos.query
      CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property
          observed ∧
        match observed with
        | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ => ProperState after.core
        | _ => True := by
  classical
  obtain ⟨currentBound, current⟩ := prefix_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet profile property bounded known
  obtain ⟨validBound, validated⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet profile property bounded known
  refine ⟨currentBound + validBound, ?_⟩
  intro extra selected chosen
  have currentAt := current (validBound + extra) selected chosen
  have validAt := validated (currentBound + extra) selected chosen
  have currentFuel : currentBound + (validBound + extra) = currentBound + validBound + extra := by omega
  have validFuel : validBound + (currentBound + extra) = currentBound + validBound + extra := by omega
  rw [currentFuel] at currentAt
  rw [validFuel] at validAt
  refine ⟨currentAt, ?_⟩
  exact SourcePruningEnumerationSelectedStep.prefix_proper
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    (currentBound + validBound + extra) selected caller before memos proper validAt.1

end MicroCFTA.SourcePruningEnumerationSharedRecursive
