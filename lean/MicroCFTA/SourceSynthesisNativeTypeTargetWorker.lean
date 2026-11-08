import MicroCFTA.SourceSynthesisNativeTypeTarget
import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound

/-!
# Actual Type target returns derive their checked graphs

The literal operand return supplies its projection and allocated Merge.
The Type target laws derive readiness at each actual returned prefix.
Native word checks apply only at that prefix. No language inventory,
future target graph, or returned annotation is an input.

Successful executable returns and reached word ranges remain explicit.
These laws do not establish completion, failure-prefix closure, or a global
original-input bound. The serial graph does not establish native lazy order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeTargetWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedTargetGraph (Fold Target FoldRanges TargetRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "PhysicalMemo" => SourceCurrentMemoMergeEffects.Stored
local notation "TypedMemo" => SourceCurrentHereditaryMerge.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

/-- Every successful literal fold derives the same checked graph from its initial Type facts. -/
theorem fold_graph (lib : Library) (p h m s n : Nat)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked width) (memo : Memo)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (physicalMemo : PhysicalMemo before.native.machine.heap memo) (typedMemo : TypedMemo (Origin lib) memo)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ seed :: paths, ForestPath (Origin lib) path values)
    (ranges : FoldRanges values seed paths before memo)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo)
    (done : SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths before memo = .done result after saved) :
    Fold values seed paths before memo result after saved := by
  induction paths generalizing before memo result after saved with
  | nil =>
      exact .nil (SourceCurrentAllocatedTargetWorkerSound.operand_sound p h m s seed values
        before memo result after saved done)
  | cons path paths ih =>
      obtain ⟨head, middle, current, first, rest⟩ :=
        (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ _ _ _).mp
          (by simpa only [SourceCurrentAllocatedTargetWorker.fold] using done)
      obtain ⟨tail, later, last, tailDone, leafDone⟩ :=
        (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ _ _ _).mp rest
      have firstGraph := SourceCurrentAllocatedTargetWorkerSound.operand_sound p h m s path values
        before memo head middle current first
      obtain ⟨middleReady, middleCosts, firstExtension, middleMemo, middleTypedMemo,
          headAvailable, headClosed, headTyped⟩ :=
        SourceSynthesisNativeTypeTarget.operand lib firstGraph ready costs physicalMemo typedMemo
          available closed (routes _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have tailRoutes : ∀ own ∈ seed :: paths, ForestPath (Origin lib) own values := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact routes _ List.mem_cons_self
        · exact routes own (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
      have tailAvailable := fun value member => firstExtension.available value (available value member)
      have tailGraph := ih middle current middleReady middleCosts middleMemo middleTypedMemo
        tailAvailable tailRoutes (ranges.1 head middle current firstGraph) tail later last tailDone
      obtain ⟨tailReady, _tailCosts, tailExtension, _tailMemo, _tailTypedMemo,
          tailResultAvailable, tailClosed, _tailTyped⟩ :=
        SourceSynthesisNativeTypeTarget.fold lib tailGraph middleReady middleCosts middleMemo middleTypedMemo
          tailAvailable closed tailRoutes
      obtain ⟨native, sameMemo⟩ := SourceCurrentAllocatedTargetWorkerSound.leaf_sound n head tail later last
        tailReady.good tailReady.idle (tailExtension.available _ headAvailable) tailResultAvailable
        headClosed tailClosed (ranges.2 head middle current tail later last firstGraph tailGraph)
        result after saved leafDone
      cases sameMemo
      exact .cons firstGraph tailGraph native

/-- A successful literal target needs no supplied completed target graph or language inventory. -/
theorem target_graph (lib : Library) (p h m s n : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) (memo : Memo)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (physicalMemo : PhysicalMemo before.native.machine.heap memo) (typedMemo : TypedMemo (Origin lib) memo)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ paths, ForestPath (Origin lib) path values)
    (ranges : TargetRanges values paths before memo)
    (result : Value Symbol Guard) (after : Checked width) (saved : Memo)
    (done : SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo = .done result after saved) :
    Target values paths before memo result after saved := by
  cases paths with
  | nil => cases done; exact .nil
  | cons seed paths =>
      exact .nonempty (fold_graph lib p h m s n values seed paths before memo ready costs physicalMemo typedMemo
        available closed routes ranges result after saved done)

end MicroCFTA.SourceSynthesisNativeTypeTargetWorker
