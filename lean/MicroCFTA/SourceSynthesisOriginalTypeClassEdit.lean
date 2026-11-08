import MicroCFTA.SourceSynthesisOriginalTypeSharedState
import MicroCFTA.SourceSynthesisNativeTypeSharedEdit

/-!
# Original source Type routes through a compiled class edit

The actual original row supplies closed available children and every guard
endpoint route. Actual class membership supplies the compiled trie routes.
The shared target state starts with empty Merge and target tables.

These laws concern successful edit graphs. They do not establish edit
completion, later source roles, failure-prefix invariants, or a global bound.
Type origin records guard provenance, not a complete generated Type grammar.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeClassEdit
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (EdgeSyntax)
open InternedFreshOrdinaryConstruction (build)
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisNativeTypeTrace (Origin cold)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceSynthesisInitialTypeFields (Program)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
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
variable {record : SourceEqualityClassOrder.Record} {results : List (Value Symbol Guard)}
variable {finish : Shared width}
include accepted built good

/-- An original application class preserves all routes through its actual compiled edit. -/
theorem application (function argument : Expression)
    (functionRole : Program lib query function) (argumentRole : Program lib query argument)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    (coherent : SourceEqualityClassOrder.Coherent record)
    (selected : record.paths ∈ (SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD [])
    (actual : SourceCurrentAllocatedSharedEditGraph.EditList record call.output.children
      (SourceCurrentAllocatedClassEditPlan.compiled record) call.output.children
      (SourceCurrentAllocatedSharedTargetState.initial (cold width heap operations)
        SourceCurrentMemoMergeGraph.empty) results finish) :
    Ready lib finish ∧
      Extension (cold width heap operations).native.machine finish.checked.native.machine ∧
      Values finish.checked.native.machine.heap results ∧ ClosedValues results ∧
      ForestRoutes (Origin lib) call.output.children results := by
  obtain ⟨ready, available, closed, endpoints⟩ :=
    SourceSynthesisOriginalTypeSharedState.application lib query signed whole accepted rootValue heap built
      operations good function argument functionRole argumentRole call
  have routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
    intro path member
    exact endpoints path ((EqualityNormalize.mem_members _ _).mpr ⟨record.paths, selected, member⟩)
  exact SourceSynthesisNativeTypeSharedEdit.list lib actual ready available closed routes
    (SourceCurrentAllocatedClassEditPlan.compiled_populated record) available closed
    (SourceCurrentHereditaryTypeEditPlan.compiled_forest_paths (Origin lib) record coherent
      call.output.children routes)

/-- An original filter class preserves all routes through its actual compiled edit. -/
theorem filter (candidates : Expression) (candidateRole : Program lib query candidates)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates])
    (coherent : SourceEqualityClassOrder.Coherent record)
    (selected : record.paths ∈ (SourceCompactGuards.sourceEqualities call.output.entry.key.constraint).getD [])
    (actual : SourceCurrentAllocatedSharedEditGraph.EditList record call.output.children
      (SourceCurrentAllocatedClassEditPlan.compiled record) call.output.children
      (SourceCurrentAllocatedSharedTargetState.initial (cold width heap operations)
        SourceCurrentMemoMergeGraph.empty) results finish) :
    Ready lib finish ∧
      Extension (cold width heap operations).native.machine finish.checked.native.machine ∧
      Values finish.checked.native.machine.heap results ∧ ClosedValues results ∧
      ForestRoutes (Origin lib) call.output.children results := by
  obtain ⟨ready, available, closed, endpoints⟩ :=
    SourceSynthesisOriginalTypeSharedState.filter lib query signed whole accepted rootValue heap built
      operations good candidates candidateRole call
  have routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
    intro path member
    exact endpoints path ((EqualityNormalize.mem_members _ _).mpr ⟨record.paths, selected, member⟩)
  exact SourceSynthesisNativeTypeSharedEdit.list lib actual ready available closed routes
    (SourceCurrentAllocatedClassEditPlan.compiled_populated record) available closed
    (SourceCurrentHereditaryTypeEditPlan.compiled_forest_paths (Origin lib) record coherent
      call.output.children routes)
end Source
end MicroCFTA.SourceSynthesisOriginalTypeClassEdit
