import MicroCFTA.SourceSynthesisOriginalProgramFieldCalls
import MicroCFTA.SourceSynthesisNativeTypeTarget

/-!
# Type origins in actual original projection and Merge targets

Accepted original construction derives costs, closed available children,
and conditional Mu stores. Original Program syntax derives nested Type
fields. Actual source class membership supplies every projection route.
The target starts with the empty Merge memo and retains the returned table.

Initial physical readiness and completed execution remain explicit.
These laws do not establish trace existence, a finite word bound, field
preservation after later edits, or native lazy evaluation order.
Type origin is guard provenance, not a complete generated Type grammar.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeTarget
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryConstruction (build)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisNativeTypeTrace (Origin cold)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceSynthesisInitialTypeFields (Program)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
variable {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
variable {width : Nat} (operations : SourceEqualityConstraintMemoAllocation.State)
variable (good : SourceCurrentAllocatedNativePhysicalCompletion.Good (cold width heap operations))
variable {paths : List EqualityNormalize.Path} {result : Value Symbol Guard} {finish : Checked width} {saved : Memo}
include accepted built good

/-- Original application syntax derives the actual Target's operand and initial memo facts. -/
theorem application (function argument : Expression)
    (functionRole : Program lib query function) (argumentRole : Program lib query argument)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    (selected : paths ∈ (SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD [])
    (actual : SourceCurrentAllocatedTargetGraph.Target call.output.children
      (paths.map (fun path => path.map Int.ofNat)) (cold width heap operations)
      SourceCurrentMemoMergeGraph.empty result finish saved) :
    Ready lib finish ∧ CostHeap finish.native.machine.heap ∧
      Extension (cold width heap operations).native.machine finish.native.machine ∧
      SourceCurrentMemoMergeEffects.Stored finish.native.machine.heap saved ∧
      SourceCurrentHereditaryMerge.Stored (Origin lib) saved ∧
      Available finish.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  obtain ⟨_semantic, costs, available, closed, _stored⟩ :=
    SourceSynthesisOriginalTypeRequired.source_context lib query signed whole accepted rootValue heap built call
  have ready := SourceSynthesisNativeTypeClosedRequests.cold_ready lib query signed whole accepted
    rootValue heap built width operations good
  apply SourceSynthesisNativeTypeTarget.target lib actual ready costs
    (SourceCurrentMemoMergeEffects.stored_empty heap)
    (SourceCurrentHereditaryMerge.stored_empty (Origin lib)) available closed
  intro path member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  have included := (EqualityNormalize.mem_members _ _).mpr ⟨paths, selected, sourceMember⟩
  rw [call.guard_eq] at included
  have endpoints := SourceSynthesisGuardRegions.application_guard_endpoints
    (typesOf lib query) function argument "app" SourceSynthesisOriginalGuardAlphabet.applicationGuard
    [typesOf lib query, arrowMarker top, function, argument] rfl
  exact SourceSynthesisOriginalProgramFieldCalls.application_paths lib query signed whole accepted
    rootValue heap built function argument functionRole argumentRole call source (endpoints.2 source included)

/-- Original filter syntax derives the actual Target's operand and initial memo facts. -/
theorem filter (candidates : Expression) (candidateRole : Program lib query candidates)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates])
    (selected : paths ∈ (SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD [])
    (actual : SourceCurrentAllocatedTargetGraph.Target call.output.children
      (paths.map (fun path => path.map Int.ofNat)) (cold width heap operations)
      SourceCurrentMemoMergeGraph.empty result finish saved) :
    Ready lib finish ∧ CostHeap finish.native.machine.heap ∧
      Extension (cold width heap operations).native.machine finish.native.machine ∧
      SourceCurrentMemoMergeEffects.Stored finish.native.machine.heap saved ∧
      SourceCurrentHereditaryMerge.Stored (Origin lib) saved ∧
      Available finish.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  obtain ⟨_semantic, costs, available, closed, _stored⟩ :=
    SourceSynthesisOriginalTypeRequired.source_context lib query signed whole accepted rootValue heap built call
  have ready := SourceSynthesisNativeTypeClosedRequests.cold_ready lib query signed whole accepted
    rootValue heap built width operations good
  apply SourceSynthesisNativeTypeTarget.target lib actual ready costs
    (SourceCurrentMemoMergeEffects.stored_empty heap)
    (SourceCurrentHereditaryMerge.stored_empty (Origin lib)) available closed
  intro path member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  have included := (EqualityNormalize.mem_members _ _).mpr ⟨paths, selected, sourceMember⟩
  rw [call.guard_eq] at included
  have endpoints := SourceSynthesisGuardRegions.filter_guard_endpoints
    candidates (typeNode top query.queryGoal) "filter" SourceSynthesisOriginalGuardAlphabet.filterGuard
    [typeNode top query.queryGoal, candidates] rfl
  exact SourceSynthesisOriginalProgramFieldCalls.filter_paths lib query signed whole accepted
    rootValue heap built candidates candidateRole call source (endpoints.2 source included)
end Source
end MicroCFTA.SourceSynthesisOriginalTypeTarget
