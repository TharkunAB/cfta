import MicroCFTA.SourceSynthesisNativeTypeSeeded
import MicroCFTA.SourceCurrentAllocatedSeededWorkerCompletion
import MicroCFTA.SourceCurrentParentGuardHeapReturns

/-!
# Joint Type and guard profiles through the actual seeded fold

The same current graph derives a complete literal worker execution. The
existing worker law retains its causal guard heap. The existing Type law
derives the result annotation and warm checked state from input routes.
No worker fuel, future heap, or native preservation callback is supplied.
The completed graph and initial structural routes remain local premises.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSeededProfile
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentHereditaryTypePaths (ForestPath)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

/-- The same actual seeded graph retains both Type facts and the causal guard heap. -/
theorem seeded (lib : Library)
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : SourceCurrentAllocatedSeededQuery.Seeded values paths before result after)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ paths, ForestPath (Origin lib) path values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      Annotated (Origin lib) result ∧ GuardHeap (Origin lib) after.native.machine.heap := by
  have good := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked ready.good) ready.semantic costs
  obtain ⟨bound, completed⟩ := SourceCurrentAllocatedSeededWorkerCompletion.seeded_uniform actual
  have retained := SourceCurrentParentGuardHeapReturns.seeded (Origin lib)
    (completed bound (Nat.le_refl _)) good available guards
  obtain ⟨next, nextCosts, extension, present, resultClosed, annotated⟩ :=
    SourceSynthesisNativeTypeSeeded.seeded lib actual ready costs available closed routes
  exact ⟨next, nextCosts, extension, present, resultClosed, annotated, retained⟩

end MicroCFTA.SourceSynthesisNativeTypeSeededProfile
