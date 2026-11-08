import MicroCFTA.SourceSynthesisNativeTypeClosedRequests
import MicroCFTA.SourceCurrentAllocatedMerge
import MicroCFTA.SourceCurrentHereditaryMergeStore

/-!
# Type origins through actual allocated warm Merge

The allocated graph supplies its literal Top-field allocation and complete
physical effects. Its erased call supplies the existing causal annotation
and Mu-store law. Both statements use the same constructor heap and result.
The returned checked state retains both native memo tables and their scopes.

The input Type annotation and existing conditional Merge memo laws remain
local premises. They do not restrict unrelated Program heap guards.
This completed-call result does not establish lazy pending publication,
runtime forcing order, failure-prefix invariants, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeMerge
open InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin origin_top)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard

/-- The actual allocated call retains the causal stores and its closed annotated output. -/
theorem merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {input output : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo}
    (lib : Library)
    (actual : SourceCurrentAllocatedMerge.Merge SourceCurrentAllocatedMerge.literalClear
      input before memo output after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (physicalMemo : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (annotationMemo : SourceCurrentHereditaryMerge.Stored (Origin lib) memo)
    (available : Available before.native.machine.heap input) (closed : input.free = [])
    (typed : Annotated (Origin lib) input) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      SourceCurrentMemoMergeEffects.Stored after.native.machine.heap saved ∧
      SourceCurrentHereditaryMerge.Stored (Origin lib) saved ∧
      Available after.native.machine.heap output ∧ output.free = [] ∧
      Annotated (Origin lib) output := by
  cases actual with
  | done call =>
    have initial := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic costs
    obtain ⟨effects, physicalAfter, returned, outputClosed⟩ := call.verified initial physicalMemo available
    obtain ⟨_, _, annotationsAfter, muStore, contract⟩ :=
      SourceCurrentHereditaryMergeStore.call (Origin lib) (origin_top lib) call.graph
        ready.semantic costs physicalMemo annotationMemo ready.stored.constructors available typed
    refine ⟨?_, effects.ready.costs,
      SourceCurrentAllocatedQueryMemo.advance_extension before _ effects,
      physicalAfter, annotationsAfter, returned, outputClosed closed, contract.2 typed⟩
    refine ⟨SourceCurrentAllocatedConjunctionMemo.advance_good before _ ready.good effects,
      effects.ready.semantic,
      SourceCurrentAllocatedConjunctionMemo.advance_scoped before _ ready.scopes,
      SourceCurrentAllocatedConjunctionMemo.advance_idle before _ ready.idle, ?_⟩
    have advanced := SourceCurrentHereditaryNativeUniversalStore.advance (Origin lib) before
      {before.native.machine with heap := _} ready.stored muStore
    exact ⟨advanced.constructors, advanced.native⟩

end MicroCFTA.SourceSynthesisNativeTypeMerge
