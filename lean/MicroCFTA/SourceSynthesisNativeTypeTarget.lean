import MicroCFTA.SourceSynthesisNativeTypeMerge
import MicroCFTA.SourceSynthesisNativeTypeOperand
import MicroCFTA.SourceCurrentAllocatedTargetGraph

/-!
# Type origins through actual projection and Merge targets

Each operand projects its captured forest and executes the actual allocated
memo-aware Merge. The fold retains the returned merge table and checked
state before its next operand and native request. Initial structural routes
derive the annotations of every generated operand. Captured memo owners keep
their conditional annotation laws at the same warm table.

Completed actual graphs and initial route certificates remain explicit.
These laws do not prove trace existence, failure-prefix closure, the source
of every later edited route, or the native lazy evaluation order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeTarget
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedTargetGraph (Operand Fold Target)
open SourceCurrentHereditaryTypePaths (ForestPath)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "PhysicalMemo" => SourceCurrentMemoMergeEffects.Stored
local notation "TypedMemo" => SourceCurrentHereditaryMerge.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

/-- The actual target operand retains the same projected value, Merge call and returned memo. -/
theorem operand (lib : Library)
    {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Operand path values before memo result after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (physicalMemo : PhysicalMemo before.native.machine.heap memo) (typedMemo : TypedMemo (Origin lib) memo)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (route : ForestPath (Origin lib) path values) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      PhysicalMemo after.native.machine.heap saved ∧ TypedMemo (Origin lib) saved ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  cases actual with
  | force projection merged =>
      obtain ⟨middleReady, middleCosts, firstExtension, projectedAvailable, projectedClosed, projectedTyped⟩ :=
        SourceSynthesisNativeTypeOperand.operand lib (.force _ _ projection) ready costs available closed route
      have middleMemo := physicalMemo.grows
        ⟨middleReady.semantic.ready, firstExtension.heap, firstExtension.history⟩
      obtain ⟨lastReady, lastCosts, lastExtension, lastMemo, lastTypedMemo, resultAvailable, resultClosed, resultTyped⟩ :=
        SourceSynthesisNativeTypeMerge.merge lib merged middleReady middleCosts middleMemo typedMemo
          projectedAvailable projectedClosed projectedTyped
      exact ⟨lastReady, lastCosts, firstExtension.trans lastExtension, lastMemo, lastTypedMemo,
        resultAvailable, resultClosed, resultTyped⟩

/-- The same actual target fold derives every intermediate operand at its returned warm state. -/
theorem fold (lib : Library)
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Fold values seed paths before memo result after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (physicalMemo : PhysicalMemo before.native.machine.heap memo) (typedMemo : TypedMemo (Origin lib) memo)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ seed :: paths, ForestPath (Origin lib) path values) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      PhysicalMemo after.native.machine.heap saved ∧ TypedMemo (Origin lib) saved ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  induction actual with
  | nil actual =>
      exact operand lib actual ready costs physicalMemo typedMemo available closed (routes _ List.mem_cons_self)
  | cons actual rest native ih =>
      obtain ⟨middleReady, middleCosts, firstExtension, middleMemo, middleTypedMemo,
          headAvailable, headClosed, headTyped⟩ :=
        operand lib actual ready costs physicalMemo typedMemo available closed
          (routes _ (List.mem_cons_of_mem _ List.mem_cons_self))
      obtain ⟨tailReady, tailCosts, tailExtension, tailMemo, tailTypedMemo,
          tailAvailable, tailClosed, tailTyped⟩ :=
        ih middleReady middleCosts middleMemo middleTypedMemo
          (fun value member => firstExtension.available value (available value member))
          (fun path member => routes path (by
            rcases List.mem_cons.mp member with rfl | member
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
      cases native with
      | run trace =>
          have query := SourceSynthesisNativeTypeClosedRequests.completed lib _ tailReady _ _
            (tailExtension.available _ headAvailable) tailAvailable headClosed tailClosed headTyped tailTyped _ _ (.run trace)
          have effects := SourceCurrentAllocatedNativeTraceEffects.effects trace tailReady.good tailReady.semantic
            tailCosts (fun _ => trivial)
          have lastMemo := tailMemo.grows
            ⟨query.2.1.semantic.ready, query.1.extension.heap, query.1.extension.history⟩
          exact ⟨query.2.1, effects.2.1.ready.costs, firstExtension.trans (tailExtension.trans query.1.extension),
            lastMemo, tailTypedMemo, query.1.physical, query.2.2, query.1.result.2⟩

/-- The actual target keeps empty targets literal and derives nonempty targets from the same fold. -/
theorem target (lib : Library)
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Target values paths before memo result after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (physicalMemo : PhysicalMemo before.native.machine.heap memo) (typedMemo : TypedMemo (Origin lib) memo)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ paths, ForestPath (Origin lib) path values) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      PhysicalMemo after.native.machine.heap saved ∧ TypedMemo (Origin lib) saved ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  cases actual with
  | nil => exact ⟨ready, costs, Extension.refl _, physicalMemo, typedMemo, empty_available _, rfl, .empty⟩
  | nonempty actual => exact fold lib actual ready costs physicalMemo typedMemo available closed routes

end MicroCFTA.SourceSynthesisNativeTypeTarget
