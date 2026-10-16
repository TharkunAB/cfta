import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEntries

/-!
# Initial resource admission for reached outer entries

Each control has its current inputs, profiles, causal stores, and supply.
The active bound protects earlier owners in both request families.
No case contains a completed graph, future read, or entry plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState (NodeRequest EdgeRequest)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape EdgeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank)
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "GPNode" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "GPEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
local notation "GPRows" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows
local notation "GPChildren" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Current input facts and remaining supply admit each of the eight controls. -/
def Admitted (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Entry (bits + 2) → Prop
  | .nodeCall request before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints request.inherited ∧
        Available before.checked.native.machine.heap request.value ∧ DNode request.value ∧
        NodeShape rows arity request.value ∧ GPNode limits request.value ∧ height request.value ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) ∧
        ActiveAbove (nodeRank request) before
  | .nodeBody request before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints request.inherited ∧
        Available before.checked.native.machine.heap request.value ∧ DNode request.value ∧
        NodeShape rows arity request.value ∧ GPNode limits request.value ∧ height request.value ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) ∧
        ActiveAbove (nodeRank request - 1) before
  | .edgeCall request before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints request.inherited ∧
        EdgeResident before.checked.native.machine.heap request.value ∧ DEdge request.value ∧
        EdgeShape rows arity request.value ∧ GPEdge limits request.value ∧ edgeHeight request.value ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound) ∧
        ActiveAbove (edgeRank request) before
  | .edgeBody request before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints request.inherited ∧
        EdgeResident before.checked.native.machine.heap request.value ∧ DEdge request.value ∧
        EdgeShape rows arity request.value ∧ GPEdge limits request.value ∧ edgeHeight request.value ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound) ∧ True
  | .rows inherited values before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints inherited ∧
        Edges before.checked.native.machine.heap values ∧ DRows values ∧
        RowsShape rows arity values ∧ GPRows limits values ∧ edgesHeight values ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (values.length * rowNodes rows arity limits bound) (values.length * rowEdges rows arity limits bound) ∧
        ∃ cap, ActiveAbove cap before ∧ ∀ edge ∈ values, edgeRank ⟨inherited, edge⟩ ≤ cap
  | .descendants inherited value before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints inherited ∧
        EdgeResident before.checked.native.machine.heap value ∧ DEdge value ∧
        EdgeShape rows arity value ∧ GPEdge limits value ∧ edgeHeight value ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (descendantsNodes rows arity limits bound) (descendantsEdges rows arity limits bound) ∧
        ∃ cap, ActiveAbove cap before ∧ ∀ child ∈ value.children, nodeRank ⟨inherited, child⟩ ≤ cap
  | .children combined values before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints combined ∧
        Values before.checked.native.machine.heap values ∧ DChildren values ∧
        ChildrenShape rows arity values ∧ GPChildren limits values ∧ childrenHeight values ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound) ∧
        ∃ cap, ActiveAbove cap before ∧ ∀ value ∈ values, nodeRank ⟨combined, value⟩ ≤ cap
  | .walk combined _index values before =>
      ∃ (inventory : Inventory) (memos : Memos) (rows arity bound : Nat) (limits : Limits),
        Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints combined ∧
        Values before.checked.native.machine.heap values ∧ DChildren values ∧
        ChildrenShape rows arity values ∧ GPChildren limits values ∧ childrenHeight values ≤ bound ∧
        Headroom bits before.checked.native.machine.heap
          (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound) ∧
        ∃ cap, ActiveAbove cap before ∧ ∀ value ∈ values, nodeRank ⟨combined, value⟩ ≤ cap

/-- Admitted parent entries derive the old numeric capacity at that exact state. -/
theorem edge_body_capacity {bits budget : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {request : EdgeRequest} {before : Caller (bits + 2)}
    (admitted : Admitted bits formulas solver (.edgeBody request before)) :
    SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget request before := by
  obtain ⟨inventory, memos, rows, arity, bound, limits,
    initial, stored, inherited, resident, _domain, profile, guards, heightBound, room, _⟩ := admitted
  exact SourceCurrentAllocatedFiniteOrdinaryParentUniformCapacity.complete bits formulas solver inventory
    initial inherited resident stored limits rows arity bound guards profile heightBound room.1 room.2

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Initial current node facts supply a root entry without an execution premise. -/
theorem node_call {bits : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {memos : Memos} (request : NodeRequest) (before : Caller (bits + 2))
    (rows arity bound : Nat) (limits : Limits)
    (initial : Context formulas solver inventory before memos) (stored : Stored before)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (profile : NodeShape rows arity request.value) (guards : GPNode limits request.value)
    (heightBound : height request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound))
    (active : ActiveAbove (nodeRank request) before) : Admitted bits formulas solver (.nodeCall request before) :=
  ⟨inventory, memos, rows, arity, bound, limits, initial, stored, inherited, available, domain,
    profile, guards, heightBound, room, active⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs
