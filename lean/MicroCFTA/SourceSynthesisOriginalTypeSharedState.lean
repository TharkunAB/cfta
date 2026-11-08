import MicroCFTA.SourceSynthesisNativeTypeSharedState
import MicroCFTA.SourceSynthesisOriginalProgramFieldCalls

/-!
# Original Type routes at the initial shared target state

Accepted original construction supplies costs, closed available children,
and the conditional Mu store. Empty native and Merge tables derive their
initial laws. The shared target slots start empty.
Original Program syntax derives nested fields. Every literal source guard
endpoint therefore supplies its structural Type route at this same state.
These laws do not establish role preservation through subsequent edits,
completed execution, failure-prefix invariants, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeSharedState
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisNativeTypeTrace (Origin cold)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceSynthesisInitialTypeFields (Program)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Original construction derives shared readiness with empty target slots and Merge table. -/
theorem initial_ready
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (width : Nat) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good (cold width heap operations)) :
    SharedReady lib (SourceCurrentAllocatedSharedTargetState.initial
      (cold width heap operations) SourceCurrentMemoMergeGraph.empty) := by
  have ready := SourceSynthesisNativeTypeClosedRequests.cold_ready lib query signed whole accepted
    rootValue heap built width operations good
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap (ordinarySymbols whole)
  exact SourceSynthesisNativeTypeSharedState.initial lib (cold width heap operations)
    SourceCurrentMemoMergeGraph.empty ready costs
    (SourceCurrentMemoMergeEffects.stored_empty heap)
    (SourceCurrentHereditaryMerge.stored_empty (Origin lib))

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
variable {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
variable {width : Nat} (operations : SourceEqualityConstraintMemoAllocation.State)
variable (good : SourceCurrentAllocatedNativePhysicalCompletion.Good (cold width heap operations))
include accepted built good

/-- Every original application guard endpoint has its Type route and initial historical state. -/
theorem application (function argument : Expression)
    (functionRole : Program lib query function) (argumentRole : Program lib query argument)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument]) :
    SharedReady lib (SourceCurrentAllocatedSharedTargetState.initial
      (cold width heap operations) SourceCurrentMemoMergeGraph.empty) ∧
    Values heap call.output.children ∧ ClosedValues call.output.children ∧
    ∀ path ∈ EqualityNormalize.members
      ((SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD []),
      ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
  obtain ⟨_, _, available, closed, _⟩ :=
    SourceSynthesisOriginalTypeRequired.source_context lib query signed whole accepted rootValue heap built call
  refine ⟨initial_ready lib query signed whole accepted rootValue heap built width operations good,
    available, closed, ?_⟩
  intro path member
  rw [call.guard_eq] at member
  have endpoints := SourceSynthesisGuardRegions.application_guard_endpoints
    (typesOf lib query) function argument "app" SourceSynthesisOriginalGuardAlphabet.applicationGuard
    [typesOf lib query, arrowMarker top, function, argument] rfl
  exact SourceSynthesisOriginalProgramFieldCalls.application_paths lib query signed whole accepted
    rootValue heap built function argument functionRole argumentRole call path (endpoints.2 path member)

/-- Every original filter guard endpoint has its Type route and initial historical state. -/
theorem filter (candidates : Expression) (candidateRole : Program lib query candidates)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates]) :
    SharedReady lib (SourceCurrentAllocatedSharedTargetState.initial
      (cold width heap operations) SourceCurrentMemoMergeGraph.empty) ∧
    Values heap call.output.children ∧ ClosedValues call.output.children ∧
    ∀ path ∈ EqualityNormalize.members
      ((SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD []),
      ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
  obtain ⟨_, _, available, closed, _⟩ :=
    SourceSynthesisOriginalTypeRequired.source_context lib query signed whole accepted rootValue heap built call
  refine ⟨initial_ready lib query signed whole accepted rootValue heap built width operations good,
    available, closed, ?_⟩
  intro path member
  rw [call.guard_eq] at member
  have endpoints := SourceSynthesisGuardRegions.filter_guard_endpoints
    candidates (typeNode top query.queryGoal) "filter" SourceSynthesisOriginalGuardAlphabet.filterGuard
    [typeNode top query.queryGoal, candidates] rfl
  exact SourceSynthesisOriginalProgramFieldCalls.filter_paths lib query signed whole accepted
    rootValue heap built candidates candidateRole call path (endpoints.2 path member)
end Source
end MicroCFTA.SourceSynthesisOriginalTypeSharedState
