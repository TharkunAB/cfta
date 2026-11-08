import MicroCFTA.SourceSynthesisNativeTypeClosedRequests
import MicroCFTA.SourceCurrentAllocatedSharedTargetState
import MicroCFTA.SourceCurrentHereditaryMerge

/-!
# Type facts at actual shared target states

Each stored target retains its available, closed, annotated value. These
facts concern literal earlier slot entries. The existing semantic target
receipts remain separate. Checked execution advances old slots through its
actual extension. A completed store adds facts for its exact returned value.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedState
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {width : Nat}

/-- Type readiness records actual native, merge, and historical target facts. -/
structure Ready (lib : Library) (state : Shared width) : Prop where
  checked : SourceSynthesisNativeTypeClosedRequests.Ready lib state.checked
  costs : CostHeap state.checked.native.machine.heap
  physicalMemo : SourceCurrentMemoMergeEffects.Stored state.checked.native.machine.heap state.memo
  typedMemo : SourceCurrentHereditaryMerge.Stored (Origin lib) state.memo
  slots : ∀ path value, state.targets path = some value →
    Available state.checked.native.machine.heap value ∧ value.free = [] ∧ Annotated (Origin lib) value

/-- The literal initial shared state has no target entry to check. -/
theorem initial (lib : Library) (checked : Checked width) (memo : Memo)
    (ready : SourceSynthesisNativeTypeClosedRequests.Ready lib checked)
    (costs : CostHeap checked.native.machine.heap)
    (physicalMemo : SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap memo)
    (typedMemo : SourceCurrentHereditaryMerge.Stored (Origin lib) memo) :
    Ready lib (SourceCurrentAllocatedSharedTargetState.initial checked memo) :=
  ⟨ready, costs, physicalMemo, typedMemo, by intro path value absent; cases absent⟩

/-- Checked advancement retains the same merge entries and every earlier target value. -/
theorem advance (lib : Library) (before : Shared width) (checked : Checked width)
    (ready : Ready lib before) (nextReady : SourceSynthesisNativeTypeClosedRequests.Ready lib checked)
    (costs : CostHeap checked.native.machine.heap)
    (extension : Extension before.checked.native.machine checked.native.machine) :
    Ready lib (SourceCurrentAllocatedSharedTargetState.advance before checked) := by
  have kept : SourceEqualityRequiredCache.Keeps before.checked.native.machine.heap checked.native.machine.heap :=
    ⟨nextReady.semantic.ready, extension.heap, extension.history⟩
  refine ⟨nextReady, costs, ready.physicalMemo.grows kept, ready.typedMemo, ?_⟩
  intro path value present
  obtain ⟨available, closed, annotated⟩ := ready.slots path value present
  exact ⟨extension.available value available, closed, annotated⟩

/-- A completed store adds its actual target and retains earlier slots through extension. -/
theorem store (lib : Library) (before : Shared width) (path : EqualityNormalize.Path)
    (value : Value Symbol Guard) (checked : Checked width) (memo : Memo)
    (ready : Ready lib before) (nextReady : SourceSynthesisNativeTypeClosedRequests.Ready lib checked)
    (costs : CostHeap checked.native.machine.heap)
    (extension : Extension before.checked.native.machine checked.native.machine)
    (physicalMemo : SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap memo)
    (typedMemo : SourceCurrentHereditaryMerge.Stored (Origin lib) memo)
    (available : Available checked.native.machine.heap value) (closed : value.free = [])
    (annotated : Annotated (Origin lib) value) :
    Ready lib (SourceCurrentAllocatedSharedTargetState.store before path value checked memo) := by
  refine ⟨nextReady, costs, physicalMemo, typedMemo, ?_⟩
  intro other target present
  by_cases same : other = path
  · subst other
    have equal : value = target := by
      simpa only [SourceCurrentAllocatedSharedTargetState.store, put, ite_true, Option.some.injEq] using present
    subst target
    exact ⟨available, closed, annotated⟩
  · have original : before.targets other = some target := by
      simpa only [SourceCurrentAllocatedSharedTargetState.store, put, same, ite_false] using present
    obtain ⟨oldAvailable, oldClosed, oldAnnotated⟩ := ready.slots other target original
    exact ⟨extension.available target oldAvailable, oldClosed, oldAnnotated⟩

end MicroCFTA.SourceSynthesisNativeTypeSharedState
