import MicroCFTA.SourceSynthesisNativeTypeOperand

/-!
# Type provenance through the actual first-seeded class fold

The fold keeps the source head projection, tail fold, and native request
in their actual order. Structural input routes select Type operands from
mixed Program forests. Each actual returned state supplies the next warm
state, including its constructor and native caches. The proof derives
annotations for generated intermediate operands and carries closedness.

Completed projection and query traces remain explicit in the actual fold.
The input routes are local structural facts, not derived here for every
edited Program forest. These laws do not prove completion, failure-prefix
closure, native lazy evaluation order, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSeeded
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedSeededQuery (Fold Seeded)
open SourceCurrentHereditaryTypePaths (ForestPath)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

/-- Actual fold states derive their generated operand facts from structural input paths. -/
theorem fold (lib : Library)
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : Fold values paths before result after) (ready : Ready lib before)
    (costs : CostHeap before.native.machine.heap) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (routes : ∀ path ∈ paths, ForestPath (Origin lib) path values) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  induction actual with
  | one operand =>
      exact SourceSynthesisNativeTypeOperand.operand lib operand ready costs available closed
        (routes _ List.mem_cons_self)
  | cons operand rest native ih =>
      obtain ⟨middleReady, middleCosts, firstExtension, headAvailable, headClosed, headAnnotated⟩ :=
        SourceSynthesisNativeTypeOperand.operand lib operand ready costs available closed
          (routes _ List.mem_cons_self)
      obtain ⟨tailReady, tailCosts, tailExtension, tailAvailable, tailClosed, tailAnnotated⟩ :=
        ih middleReady middleCosts (fun value member => firstExtension.available value (available value member))
          (fun path member => routes path (List.mem_cons_of_mem _ member))
      have query := SourceSynthesisNativeTypeClosedRequests.completed lib _ tailReady _ _
        (tailExtension.available _ headAvailable) tailAvailable headClosed tailClosed
        headAnnotated tailAnnotated _ _ (.run native)
      have effects := SourceCurrentAllocatedNativeTraceEffects.effects native tailReady.good tailReady.semantic
        tailCosts (fun _ => trivial)
      exact ⟨query.2.1, effects.2.1.ready.costs,
        firstExtension.trans (tailExtension.trans query.1.extension),
        query.1.physical, query.2.2, query.1.result.2⟩

/-- Literal empty input and the source first-seed rotation retain the same Type result facts. -/
theorem seeded (lib : Library)
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : Seeded values paths before result after) (ready : Ready lib before)
    (costs : CostHeap before.native.machine.heap) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (routes : ∀ path ∈ paths, ForestPath (Origin lib) path values) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  cases actual with
  | nil => exact ⟨ready, costs, Extension.refl _, empty_available _, rfl, .empty⟩
  | nonempty actual =>
      apply fold lib actual ready costs available closed
      intro path member
      exact routes path (by simpa [List.mem_append, List.mem_cons, or_comm] using member)

end MicroCFTA.SourceSynthesisNativeTypeSeeded
