import MicroCFTA.SourceCurrentAllocatedPartialWorkerActual
import MicroCFTA.SourcePruningEnumerationPartialActualArity

/-!
# Arity at literal completed recursive worker returns

Each theorem retains the complete original admission and result.
The actual read graph derives arity for the same returned native heap.
Only a genuine initial arity-valid heap is added to the input.
-/
namespace MicroCFTA.SourcePruningEnumerationPartialWorkerArity
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecksComposition
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialWorkerStability (bind_done_iff)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)


/-- The literal completed nodeCall retains its full receipt and derives returned arity. -/
theorem nodeCall_verified
    {fuel g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget request before)
    (done : nodeCall fuel g s r e p h m c n budget request before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.nodeCall_verified formulas solver initial inheritedReady available ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.node_call_heap formulas solver reads inventory checks initial
      inheritedReady available heap⟩

/-- The literal completed nodeBody retains its full receipt and derives returned arity. -/
theorem nodeBody_verified
    {fuel g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeBody fuel g s r e p h m c n budget request before)
    (done : nodeBody fuel g s r e p h m c n budget request before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : NodeBody budget request before result after,
      NodeBodyReads formulas solver actual memos final ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.nodeBody_verified formulas solver initial inheritedReady available ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.node_body_heap formulas solver reads inventory checks initial
      inheritedReady available heap⟩

/-- The literal completed edgeCall retains its full receipt and derives returned arity. -/
theorem edgeCall_verified
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall fuel g s r e p h m c n budget request before)
    (done : edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : EdgeCall budget request before result after,
      EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.edgeCall_verified formulas solver initial inheritedReady resident ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.edge_call_heap formulas solver reads inventory checks initial
      inheritedReady resident heap⟩

/-- The literal completed edgeBody retains its full receipt and derives returned arity. -/
theorem edgeBody_verified
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeBody fuel g s r e p h m c n budget request before)
    (done : edgeBody fuel g s r e p h m c n budget request before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : EdgeBody budget request before result after,
      EdgeBodyReads formulas solver actual memos final ∧ Checks (edgeBodyTrace actual) ∧
      Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.edgeBody_verified formulas solver initial inheritedReady resident ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.edge_body_heap formulas solver reads inventory checks initial
      inheritedReady resident heap⟩

/-- The literal completed rows retains its full receipt and derives returned arity. -/
theorem rows_verified
    {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {values : List Edge} {before after : Caller width} {result : List Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.rows fuel g s r e p h m c n budget inherited values before)
    (done : rows fuel g s r e p h m c n budget inherited values before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : Rows budget inherited values before result after,
      RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual) ∧
      Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap result ∧ SourceCurrentAllocatedPartialForestLanguage.RowsLaw formulas solver actual ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.rows_verified formulas solver initial inheritedReady resident ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.rows_heap formulas solver reads inventory checks initial
      inheritedReady resident heap⟩

/-- The literal completed descendants retains its full receipt and derives returned arity. -/
theorem descendants_verified
    {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {value : Edge} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Resident before.checked.native.machine.heap value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.descendants fuel g s r e p h m c n budget inherited value before)
    (done : descendants fuel g s r e p h m c n budget inherited value before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : Descendants budget inherited value before result after,
      DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
      Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver ⟨inherited, value⟩ result ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.descendants_verified formulas solver initial inheritedReady resident ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.descendants_heap formulas solver reads inventory checks initial
      inheritedReady resident heap⟩

/-- The literal completed children retains its full receipt and derives returned arity. -/
theorem children_verified
    {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {values : List Node} {before after : Caller width} {result : List Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.children fuel g s r e p h m c n budget combined values before)
    (done : children fuel g s r e p h m c n budget combined values before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : Children budget combined values before result after,
      ChildrenReads formulas solver actual memos final ∧ Checks (childrenTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap result ∧ SourceCurrentAllocatedPartialWalkLanguage.ChildrenLaw formulas solver actual ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.children_verified formulas solver initial inheritedReady available ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.children_heap formulas solver reads inventory checks initial
      inheritedReady available heap⟩

/-- The literal completed walk retains its full receipt and derives returned arity. -/
theorem walk_verified
    {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values : List Node} {before after : Caller width} {result : List Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.walk fuel g s r e p h m c n budget combined index values before)
    (done : walk fuel g s r e p h m c n budget combined index values before = .done result after)
    (heap : Heap before.checked.native.machine.heap) :
    ∃ next final, ∃ actual : Walk budget combined index values before result after,
      WalkReads formulas solver actual memos final ∧ Checks (walkTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap result ∧ SourceCurrentAllocatedPartialWalkLanguage.WalkLaw formulas solver actual ∧
      Heap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.walk_verified formulas solver initial inheritedReady available ranges done
  exact ⟨next, final, actual, reads, checks, post, output, law,
    SourcePruningEnumerationPartialActualArity.walk_heap formulas solver reads inventory checks initial
      inheritedReady available heap⟩

end MicroCFTA.SourcePruningEnumerationPartialWorkerArity
