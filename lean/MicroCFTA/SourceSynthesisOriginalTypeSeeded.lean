import MicroCFTA.SourceSynthesisOriginalProgramFieldCalls
import MicroCFTA.SourceSynthesisNativeTypeSeeded

/-!
# Type origins in actual original seeded class queries

Accepted original construction supplies the costs, closed children, available
children, conditional Mu store, and initial semantic and memo facts. Exact
original Program syntax derives the nested annotation fields. Every selected
source region therefore supplies its structural projection certificate.
The same completed seeded fold retains its changing warm state.

Initial physical readiness and completed execution remain explicit. These
laws do not prove a finite word bound, trace existence, closure after later
Program edits, or the native lazy evaluation order. Type origin records guard
provenance. It does not establish the full generated Type grammar.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeSeeded
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
variable {paths : List EqualityNormalize.Path} {result : Value Symbol Guard} {finish : Checked width}
include accepted built good

/-- Original application syntax derives all operand facts for the same completed seeded query. -/
theorem application (function argument : Expression)
    (functionRole : Program lib query function) (argumentRole : Program lib query argument)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    (selected : paths ∈ (SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD [])
    (actual : SourceCurrentAllocatedSeededQuery.Seeded call.output.children
      (paths.map (fun path => path.map Int.ofNat)) (cold width heap operations) result finish) :
    Ready lib finish ∧ CostHeap finish.native.machine.heap ∧
      Extension (cold width heap operations).native.machine finish.native.machine ∧
      Available finish.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  obtain ⟨_semantic, costs, available, closed, _stored⟩ :=
    SourceSynthesisOriginalTypeRequired.source_context lib query signed whole accepted rootValue heap built call
  have ready := SourceSynthesisNativeTypeClosedRequests.cold_ready lib query signed whole accepted
    rootValue heap built width operations good
  apply SourceSynthesisNativeTypeSeeded.seeded lib actual ready costs available closed
  intro path member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  have included := (EqualityNormalize.mem_members _ _).mpr ⟨paths, selected, sourceMember⟩
  rw [call.guard_eq] at included
  have endpoints := SourceSynthesisGuardRegions.application_guard_endpoints
    (typesOf lib query) function argument "app" SourceSynthesisOriginalGuardAlphabet.applicationGuard
    [typesOf lib query, arrowMarker top, function, argument] rfl
  exact SourceSynthesisOriginalProgramFieldCalls.application_paths lib query signed whole accepted
    rootValue heap built function argument functionRole argumentRole call source (endpoints.2 source included)

/-- Original filter syntax derives all operand facts for the same completed seeded query. -/
theorem filter (candidates : Expression) (candidateRole : Program lib query candidates)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates])
    (selected : paths ∈ (SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD [])
    (actual : SourceCurrentAllocatedSeededQuery.Seeded call.output.children
      (paths.map (fun path => path.map Int.ofNat)) (cold width heap operations) result finish) :
    Ready lib finish ∧ CostHeap finish.native.machine.heap ∧
      Extension (cold width heap operations).native.machine finish.native.machine ∧
      Available finish.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  obtain ⟨_semantic, costs, available, closed, _stored⟩ :=
    SourceSynthesisOriginalTypeRequired.source_context lib query signed whole accepted rootValue heap built call
  have ready := SourceSynthesisNativeTypeClosedRequests.cold_ready lib query signed whole accepted
    rootValue heap built width operations good
  apply SourceSynthesisNativeTypeSeeded.seeded lib actual ready costs available closed
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
end MicroCFTA.SourceSynthesisOriginalTypeSeeded
