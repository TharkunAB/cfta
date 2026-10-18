import MicroCFTA.SourceCurrentPositiveForestProjectionOrigins
import MicroCFTA.SourceCurrentActualMergeOperandOrigins

/-!
# Original input anchors of positive target operand rows

A literal target operand supplies its actual forest projection and Merge.
The false primary receipt names the same original forest. A positive returned
row retains a full source row along an indexed ordinary route. Recursive Merge
requests take that source row's children in their original order. Each input
child has smaller mass than the selected original forest value.

Returned children can differ from these input anchors. The actual Merge writer
can precede the current call. Its raw history certificate remains explicit.
The theorem does not identify an earlier edited forest with an initial outer
input, and it does not establish all selected-edit renewal or termination.
-/
namespace MicroCFTA.SourceCurrentActualTargetOperandSourceOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead
open SourceCurrentMergePositiveRowOrigins
open EndpointStatefulGateTrace
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A literal positive operand return retains an original forest row and its strictly smaller recursive Merge inputs. -/
theorem operand {projectionFuel readFuel mergeFuel selectionFuel : Nat}
    (index : Nat) (path : EqualityNormalize.Path) (values : List Node)
    (before after : Checked width) (memo saved : Memo) (result : Node)
    (actual : SourceCurrentAllocatedTargetWorker.operand projectionFuel readFuel mergeFuel selectionFuel
      ((index :: path).map Int.ofNat) values before memo = .done result after saved)
    (semantic : SemanticReady before.native.machine.heap) (costs : CostHeap before.native.machine.heap)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (raw : Raw literalClear top memo)
    (guards : Guards before.native.machine.heap) (gateBefore gateAfter : Heap)
    (gate : PathTrace source reaches values (index :: path) gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore)
    (initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal gateBefore)
    (initialAvailable : Values gateBefore values) (retained : Grows gateAfter before.native.machine.heap)
    (row : Row) (member : row ∈ nodeEdges result) (records : List SourceEqualityClassOrder.Record)
    (positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records))
    (nonempty : records ≠ []) :
    Raw literalClear top saved ∧
    ∃ (projected : Node) (middle : Checked width) (sourceValue : Node) (sourceIndex : Nat) (original : Row),
      SourceCurrentAllocatedTargetWorker.projection projectionFuel readFuel ((index :: path).map Int.ofNat)
        values before memo = .done projected middle memo ∧
      SourceCurrentAllocatedTargetWorker.merge mergeFuel selectionFuel projected middle memo = .done result after saved ∧
      Forest ((index :: path).map Int.ofNat) values before.native.machine.heap projected middle.native.machine.heap ∧
      Writer literalClear top projected result ∧ values[index]? = some sourceValue ∧
      (nodeEdges projected)[sourceIndex]? = some original ∧
      SourceEqualityProjectionGraph.Project (path.map Int.ofNat) sourceValue before.native.machine.heap projected
        middle.native.machine.heap ∧
      SourceCurrentPositiveProjectionSourceRoute.Route (path.map Int.ofNat) sourceValue original ∧
      row.entry.key.symbol = original.entry.key.symbol ∧ row.entry.key.constraint = original.entry.key.constraint ∧
      (∀ child ∈ original.children, InternedValueMass.value child < InternedValueMass.value sourceValue) ∧
      (row = original ∨ ∃ start current finish final,
        SourceCurrentMemoMergeGraph.Run literalClear top
          (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request original.children)
          start current row.children finish final) := by
  obtain ⟨finalRaw,projected,middle,projectionDone,mergeDone,graph,writer,
      sourceIndex,original,found,symbol,guard,children⟩ :=
    SourceCurrentActualMergeOperandOrigins.operand actual semantic costs stored available raw row member
      records positive nonempty
  have effects := SourceEqualityProjectionCosts.forest_effects graph semantic costs available
  have middleGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain graph semantic costs available guards
  have selected : original ∈ nodeEdges projected := List.mem_of_getElem? found
  have nonPlain : ¬ Plain original.entry.key.constraint := by
    intro accepted
    have emptyOwn := SourceCurrentHereditaryUnconstrained.plain_physical _ accepted
    rw [← guard,positive] at emptyOwn
    exact nonempty (Option.some.inj (Except.ok.inj emptyOwn))
  have read : Read projected middle.native.machine.heap (nodeEdges projected) middle.native.machine.heap := by
    cases projected with
    | empty | node => exact .done 0 rfl
    | reference | union | mu => cases selected
  obtain ⟨sourceValue,atIndex,project,route,smaller⟩ :=
    SourceCurrentPositiveForestProjectionOrigins.forest_read index path values gateBefore gateAfter
      before.native.machine.heap middle.native.machine.heap projected gate initialSemantic initialNormal initialAvailable
      retained semantic costs available guards graph middle.native.machine.heap effects.2.1 middleGuards
      (pure_keeps _ effects.2.1.ready) (nodeEdges projected) middle.native.machine.heap read original selected nonPlain
  exact ⟨finalRaw,projected,middle,sourceValue,sourceIndex,original,projectionDone,mergeDone,graph,writer,
    atIndex,found,project,route,symbol,guard,smaller,children⟩

end MicroCFTA.SourceCurrentActualTargetOperandSourceOrigins
