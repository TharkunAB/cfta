import MicroCFTA.SourceCurrentMergePositiveRowOrigins
import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Positive row sources of actual allocated target operands

A literal operand return supplies its projection and merge at their exact
states. The initial merge certificate records actual earlier writers.
Physical stored entries alone do not supply this certificate. The source
anchor is the projected value. Original forest occurrences remain separate.
-/
namespace MicroCFTA.SourceCurrentActualMergeOperandOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentMergePositiveRowOrigins
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem stages {p h m s path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo =
      .done result after saved)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    ∃ (projected : Node) (middle : Checked width),
      SourceCurrentAllocatedTargetWorker.projection p h path values before memo = .done projected middle memo ∧
      SourceCurrentAllocatedTargetWorker.merge m s projected middle memo = .done result after saved ∧
      SourceEqualityProjectionGraph.Forest path values before.native.machine.heap projected middle.native.machine.heap ∧
      SourceEqualityRequiredSemanticCache.SemanticReady middle.native.machine.heap ∧
      InternedFreshOrdinaryCostHeap.Heap middle.native.machine.heap ∧
      Available middle.native.machine.heap projected ∧
      SourceCurrentMemoMergeEffects.Stored middle.native.machine.heap memo ∧
      SourceCurrentMemoMergeGraph.Call literalClear top projected middle.native.machine.heap memo
        result after.native.machine.heap saved := by
  obtain ⟨projected,middle,current,projectionDone,mergeDone⟩ :=
    (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
  obtain ⟨heap,graph,shape,sameMemo⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound
    p h path values before memo projected middle current projectionDone
  subst current
  have facts := SourceEqualityProjectionCosts.forest_effects graph semantic costs available
  have mergeGraph := SourceCurrentAllocatedTargetWorkerSound.merge_sound
    m s projected middle memo result after saved mergeDone
  have middleHeap : middle.native.machine.heap = heap := by rw [shape]; rfl
  refine ⟨projected,middle,projectionDone,mergeDone,?_,?_,?_,?_,?_,?_⟩
  · simpa only [middleHeap] using graph
  · simpa only [middleHeap] using facts.2.1
  · simpa only [middleHeap] using facts.2.2.1
  · simpa only [middleHeap] using facts.2.2.2
  · simpa only [middleHeap] using stored.grows facts.1
  · cases mergeGraph with
    | done called => exact called.graph

/-- A positive literal operand return supplies its actual projected source and earlier merge writer. -/
theorem operand {p h m s path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo =
      .done result after saved)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (raw : Raw literalClear top memo)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges result)
    (records : List SourceEqualityClassOrder.Record)
    (positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records))
    (nonempty : records ≠ []) :
    Raw literalClear top saved ∧
    ∃ (projected : Node) (middle : Checked width),
      SourceCurrentAllocatedTargetWorker.projection p h path values before memo = .done projected middle memo ∧
      SourceCurrentAllocatedTargetWorker.merge m s projected middle memo = .done result after saved ∧
      SourceEqualityProjectionGraph.Forest path values before.native.machine.heap projected middle.native.machine.heap ∧
      Writer literalClear top projected result ∧
      ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard), (nodeEdges projected)[sourceIndex]? = some original ∧
        row.entry.key.symbol = original.entry.key.symbol ∧ row.entry.key.constraint = original.entry.key.constraint ∧
        (row = original ∨ ∃ start current finish final,
          SourceCurrentMemoMergeGraph.Run literalClear top
            (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request original.children)
            start current row.children finish final) := by
  obtain ⟨projected,middle,projectionDone,mergeDone,graph,known,ranked,admitted,physical,called⟩ :=
    stages actual semantic costs stored available
  obtain ⟨finalRaw,writer⟩ := call called known ranked physical raw admitted
  have nonTop : row.entry.key.constraint ≠ top := by
    intro same
    have emptyOwn : SourceEqualityPhysicalPayload.own (top : Guard) = .ok (some []) := rfl
    rw [same,emptyOwn] at positive
    exact nonempty (Option.some.inj (Except.ok.inj positive)).symm
  exact ⟨finalRaw,projected,middle,projectionDone,mergeDone,graph,writer,
    SourceCurrentMergePositiveRowOrigins.positive writer row member nonTop⟩

end MicroCFTA.SourceCurrentActualMergeOperandOrigins
