import MicroCFTA.SourceSynthesisNativeTypeClosedRequests
import MicroCFTA.SourceCurrentHereditaryTypePaths
import MicroCFTA.SourceCurrentAllocatedSeededQuery
import MicroCFTA.SourceCurrentOpenProjectionFields

/-!
# Type origins through an actual seeded-query operand

The literal projection advances the constructor heap at the same equality
operations and native tables. Its actual graph derives the physical effects,
closed result, conditional Mu store, and Type-origin annotation.

The source route certificate permits unannotated ordinary ancestors.
It does not assign Type roles to arbitrary Program unions or Mu ancestors.
Initial costs and the static selected route remain local premises.
No future readiness, stored result, or word-range plan is supplied.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeOperand
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready

/-- The same actual operand preserves warm query facts and returns its annotated closed value. -/
theorem operand [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {result : Value Symbol Guard}
    (lib : Library)
    (actual : SourceCurrentAllocatedSeededQuery.Operand path values before result after)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (selected : SourceCurrentHereditaryTypePaths.ForestPath (Origin lib) path values) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      Annotated (Origin lib) result := by
  cases actual with
  | force heap projected =>
    have checked := SourceEqualityProjectionCosts.forest_effects projected ready.semantic costs available
    have fields : SourceCurrentConjunctionEquality.Fields before.operations heap :=
      SourceCurrentOpenProjectionFields.forest
        (SourceCurrentConjunctionEquality.FieldAvailable before.operations)
        projected ready.semantic costs available ready.good.fields
    let next : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula :=
      ⟨heap, before.operations⟩
    have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) next :=
      ⟨checked.1, ⟨checked.2.1, checked.2.2.1, ready.good.operations, fields⟩,
        SourceEqualityConstraintMemoAllocation.grows_refl before.operations⟩
    have typed := SourceCurrentHereditaryTypePaths.forest (Origin lib) projected ready.semantic
      available closed ready.stored.constructors selected
    have resultClosed : result.free = [] := by
      obtain ⟨value, final, completed, _, _, _, valueClosed⟩ :=
        SourceEqualityProjectionComplete.forest_complete path values before.native.machine.heap
          ready.semantic available closed
      have same := (SourceEqualityProjectionAPI.forest_unique projected completed).1
      rw [same]
      exact valueClosed
    have stored : SourceCurrentHereditaryNativeUniversalStore.Stored (Origin lib)
        (advancePhysical before next) :=
      SourceCurrentHereditaryNativeUniversalStore.advance (Origin lib) before
        {before.native.machine with heap := heap} ready.stored typed.1
    have nextReady : Ready lib (advancePhysical before next) :=
      ⟨SourceCurrentAllocatedConjunctionMemo.advance_good before next ready.good effects,
        checked.2.1,
        SourceCurrentAllocatedConjunctionMemo.advance_scoped before next ready.scopes,
        SourceCurrentAllocatedConjunctionMemo.advance_idle before next ready.idle,
        stored⟩
    exact ⟨nextReady, checked.2.2.1,
      SourceCurrentAllocatedQueryMemo.advance_extension before next effects,
      checked.2.2.2, resultClosed, typed.2⟩

end MicroCFTA.SourceSynthesisNativeTypeOperand
