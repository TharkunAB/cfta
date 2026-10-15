import MicroCFTA.SourceMergedProbeWorker
import MicroCFTA.SourceEqualitySharedTargetLeaf

/-!
# Filtered Mu probes through actual shared target demands

Operand projection and general merging retain the actual warm native state.
The first-seeded right fold retains filtered probes through each native request.
First forcing stores its actual target. Reuse changes no heap or target slot.
-/
namespace MicroCFTA.SourceEqualityProbeTarget
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityDemandTarget
open InternedFreshOrdinaryProbeHeap (Heap)

/-- An actual general merge request retains filtered probes at its returned native cache. -/
theorem merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {value result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEqualityNativeMerge.Merge clear top value before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap value) (closed : value.free = []) (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | done fuel actual =>
      exact SourceMergedProbeWorker.execute_heap clear top fuel value before.machine.heap
        ready.semantic available closed result _ actual heap

/-- Actual captured-forest projection and merging preserve the same probe invariant. -/
theorem operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | force projection merged =>
      have projected := SourceEqualityNativeProjection.forest_lift before ready _ values _ _ projection available closed
      have projectedHeap := SourceEqualityProbeProjection.forest projection ready.semantic available closed heap
      exact merge merged projected.1 projected.2.2.1 projected.2.2.2.1 projectedHeap

/-- The actual first-seeded right fold preserves filtered probes through every demanded operand and native step. -/
theorem fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {seed : List Int} {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  induction trace with
  | nil seedDemand => exact operand seedDemand ready available closed heap
  | @cons path before value middle paths tail later result after demanded rest step ih =>
      have first := demanded.effects ready available closed
      have firstHeap := operand demanded ready available closed heap
      have remaining := rest.effects first.1 (fun value member => first.2.1.available value (available value member)) closed
      have remainingHeap := ih first.1 (fun value member => first.2.1.available value (available value member)) firstHeap
      exact SourceEqualityNativeProbeScoped.step step remaining.1
        (remaining.2.1.available value first.2.2.1) remaining.2.2.1 remainingHeap

/-- Complete actual source targets retain filtered probes without an assumed target-output invariant. -/
theorem target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | nil => exact heap
  | cons actual => exact fold actual ready available closed heap

/-- First forcing derives preservation from actual captured scope; a hit keeps the heap unchanged. -/
theorem force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : SourceEqualitySharedTargetForce.Force emptyGuard conjoin clear top record values path before value after)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (closed : ClosedValues values) (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | hit => exact heap
  | miss _ actual =>
      exact target actual ready.native
        (fun value member => ready.captured.available value (known value member)) closed heap

/-- A shared edit leaf preserves filtered probes through actual target forcing and the subsequent native request. -/
theorem leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : SourceEqualitySharedTargetLeaf.Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (closed : ClosedValues values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known closed member
      have firstHeap := force forced ready known closed heap
      exact SourceEqualityNativeProbeScoped.step step first.1.native first.2.2.1
        (first.2.1.available input available) firstHeap

end MicroCFTA.SourceEqualityProbeTarget
