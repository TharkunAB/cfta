import MicroCFTA.SourceSynthesisNativeTypeClosedRequests
import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceCurrentGateGuard

/-!
# Type-native readiness through actual class gates

The actual gate retains its causal body-to-probe guard heap. This heap
derives the conditional Mu store at the returned constructor heap. The same
physical effects advance the checked state and retain its native cells.
No Type annotation is required for unrelated Program rows or forest items.
These completed local traces do not establish whole-scan completion.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeGate
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
variable {width : Nat}

private theorem advance (lib : Library) (before : Checked width) (heap : Heap)
    (ready : Ready lib before)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) ⟨heap, before.operations⟩)
    (guards : GuardHeap (Origin lib) heap) :
    Ready lib (advanceHeap before heap) ∧ CostHeap heap ∧
      Extension before.native.machine (advanceHeap before heap).native.machine := by
  have stored := SourceCurrentHereditaryNativeUniversalStore.advance (Origin lib) before
    {before.native.machine with heap := heap} ready.stored
      (SourceCurrentConstrainedCapGuardNative.stored (Origin lib) heap guards)
  exact ⟨⟨SourceCurrentAllocatedConjunctionMemo.advance_good before _ ready.good effects,
    effects.ready.semantic,
    SourceCurrentAllocatedConjunctionMemo.advance_scoped before _ ready.scopes,
    SourceCurrentAllocatedConjunctionMemo.advance_idle before _ ready.idle, stored⟩,
    effects.ready.costs, SourceCurrentAllocatedQueryMemo.advance_extension before _ effects⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The primary gate retains Type-native readiness at its exact advanced checked state. -/
theorem primary (lib : Library) (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before : Checked width} {heap : Heap} {answer : Bool}
    (actual : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap answer heap)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib (advanceHeap before heap) ∧ CostHeap heap ∧
      Extension before.native.machine (advanceHeap before heap).native.machine ∧
      GuardHeap (Origin lib) heap ∧ Values heap values := by
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic costs
  have effects := SourceCurrentAllocatedGateFields.primary_class unconstrained reaches actual physicalReady available
  have retained := SourceCurrentGateGuard.primary (Origin lib) unconstrained reaches actual
    ready.semantic costs available guards
  obtain ⟨next, nextCosts, extension⟩ := advance lib before heap ready effects.1 retained
  exact ⟨next, nextCosts, extension, retained, effects.2⟩

/-- The secondary gate retains the same causal stores and exact native memo ownership. -/
theorem secondary (lib : Library) (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before : Checked width} {heap : Heap} {answer : Bool}
    (actual : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths
      before.native.machine.heap answer heap)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib (advanceHeap before heap) ∧ CostHeap heap ∧
      Extension before.native.machine (advanceHeap before heap).native.machine ∧
      GuardHeap (Origin lib) heap ∧ Values heap values := by
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic costs
  have effects := SourceCurrentAllocatedGateFields.secondary_class unconstrained actual physicalReady available
  have retained := SourceCurrentGateGuard.secondary (Origin lib) unconstrained actual
    ready.semantic costs available guards
  obtain ⟨next, nextCosts, extension⟩ := advance lib before heap ready effects.1 retained
  exact ⟨next, nextCosts, extension, retained, effects.2⟩

end MicroCFTA.SourceSynthesisNativeTypeGate
