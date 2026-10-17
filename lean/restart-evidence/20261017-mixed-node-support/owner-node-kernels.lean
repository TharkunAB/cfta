import MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainNode

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MixedPlainNodeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialConditionalDomain (OwnEmpty Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove)
open SourceCurrentAllocatedPartialActiveOrder (nodeRank edgeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Region" => SourceEqualityPartialPlainRegion.Region
local notation "Stable" => SourceCurrentAllocatedPartialWorkerCompletion.StableRun
local notation "cold" => SourceCurrentAllocatedPartialState.initial
local notation "Worker" => SourceCurrentAllocatedPartialWorker.nodeCall
variable {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def busy (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (inherited : EqValue) (cap : Node) : Caller width :=
  (beginNode ⟨inherited, cap⟩ (cold checked memo fourth)).2.2

private theorem busy_active (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (inherited : EqValue) (cap : Node) (notRegion : ¬ Region cap) (rank : Nat) :
    ActiveAbove rank (busy checked memo fourth inherited cap) := by
  constructor
  · intro handle owner found region
    by_cases zero : handle = 0
    · subst handle
      have cell : (busy checked memo fourth inherited cap).nodeResults.cells 0 =
          some ⟨⟨inherited, cap⟩, .evaluating⟩ := rfl
      have same := Option.some.inj (cell.symm.trans found)
      cases same
      exact (notRegion region).elim
    · simp [busy, beginNode, SourceCurrentAllocatedPartialState.initial, FlatMemoThunk.empty, FlatMemoThunk.lookupOrInsert,
        FlatMemoThunk.demand, FlatMemoThunk.setStatus, put, zero] at found
  · intro handle owner found
    cases found

/-- An actual busy cap publication does not block a constructed ordinary row and descendant traversal. -/
theorem ordinary_after_cap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (inventory : Inventory) (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) (memos : Memos)
    (budget : Nat) (inherited : EqValue) (cap : Node) (entry) (row : Edge) (child : Node) (depth free)
    (initial : Context formulas solver inventory (cold checked memo fourth) memos)
    (inheritedReady : EqReady checked.operations.constraints inherited)
    (capAvailable : Available checked.native.machine.heap cap) (notRegion : ¬ Region cap)
    (available : Available checked.native.machine.heap (.node entry [row] depth free))
    (emptyOwn : OwnEmpty row) (children : row.children = [child]) (region : Region child)
    (capBelow : nodeRank ⟨inherited, cap⟩ ≤ nodeRank ⟨inherited, .node entry [row] depth free⟩) :
    ∃ result after next final,
      Stable (fun f g s r e p h m c n => Worker f g s r e p h m c n budget
        ⟨inherited, .node entry [row] depth free⟩ (busy checked memo fourth inherited cap)) result after ∧
      ∃ actual : NodeCall budget ⟨inherited, .node entry [row] depth free⟩
          (busy checked memo fourth inherited cap) result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next (busy checked memo fourth inherited cap) after final ∧
        Available after.checked.native.machine.heap result ∧ Stored after ∧
        ActiveAbove (nodeRank ⟨inherited, .node entry [row] depth free⟩) after ∧
        NodeLaw formulas solver ⟨inherited, .node entry [row] depth free⟩ result ∧
        after.nodeResults.cells 0 = some ⟨⟨inherited, cap⟩, .evaluating⟩ ∧
        ¬ SourceCurrentAllocatedPartialActiveOrder.ActiveAbove (nodeRank ⟨inherited, .node entry [row] depth free⟩)
          (busy checked memo fourth inherited cap) := by
  have started : beginNode ⟨inherited, cap⟩ (cold checked memo fourth) =
      (0, .evaluate ⟨inherited, cap⟩, busy checked memo fourth inherited cap) := rfl
  obtain ⟨current, _owner, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
    (request := ⟨inherited, cap⟩) initial inheritedReady capAvailable started
  have childRegions : SourceEqualityPartialPlainRegion.Children row.children := by
    rw [children]
    exact .cons region .nil
  have rows : SourceEqualityPartialPlainRegion.Rows [row] :=
    .cons (SourceEqualityPartialPlainAnnotations.physical emptyOwn) childRegions .nil
  have store : Stored (busy checked memo fourth inherited cap) :=
    (SourceCurrentAllocatedPartialConditionalDomain.initial checked memo fourth).beginNode ⟨inherited, cap⟩
  have active := busy_active checked memo fourth inherited cap notRegion
    (nodeRank ⟨inherited, .node entry [row] depth free⟩)
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, law⟩ :=
    SourceCurrentAllocatedPartialConditionalPlainNode.finite formulas solver budget
      ⟨inherited, .node entry [row] depth free⟩ current inheritedReady available (.ordinary rows) store active
  have frame := SourceCurrentAllocatedPartialFrames.node_call actual
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid current.sound.valid)
  have cell : (busy checked memo fourth inherited cap).nodeResults.cells 0 = some ⟨⟨inherited, cap⟩, .evaluating⟩ := rfl
  refine ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained,
    SourceCurrentAllocatedPartialConditionalFrames.node_call actual active, law, frame.node_running 0 _ cell, ?_⟩
  intro old
  have impossible := old.nodes 0 ⟨inherited, cap⟩ (by simp) cell
  omega

/-- Local hereditary row facts construct the whole descendant suffix and its semantic receipt. -/
theorem hereditary_descendants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (inherited : EqValue) (edge : Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap edge)
    (annotated : SourceCurrentHereditaryConstructors.Edge (fun guard => SourceMemoGate.plain guard = true) edge)
    (closed : MergedColdReaderClosedInputs.ClosedValues edge.children)
    (stored : Stored before) (active : ActiveAbove (edgeRank ⟨inherited, edge⟩) before) :
    ∃ result after next final,
      Stable (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.descendants
        f g s r e p h m c n budget inherited edge before) result after ∧
      ∃ actual : Descendants budget inherited edge before result after,
        DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ ActiveAbove (edgeRank ⟨inherited, edge⟩) after ∧ EdgeLaw formulas solver ⟨inherited, edge⟩ result := by
  have plain := SourceCurrentAllocatedPartialHereditaryPlainEdge.plain_edge before.checked.native.machine.heap
    initial.ready.semantic.ready.semantic.1.normal.facts edge resident annotated closed
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, law⟩ :=
    SourceCurrentAllocatedPartialConditionalPlainNode.descendants_finite formulas solver budget inherited edge initial
      inheritedReady resident plain.2 stored active
  exact ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained,
    SourceCurrentAllocatedPartialConditionalFrames.descendants actual active, law⟩

end MicroCFTA.MixedPlainNodeKernels

#print axioms MicroCFTA.MixedPlainNodeKernels.ordinary_after_cap
#check @MicroCFTA.MixedPlainNodeKernels.ordinary_after_cap
#print axioms MicroCFTA.MixedPlainNodeKernels.hereditary_descendants
#check @MicroCFTA.MixedPlainNodeKernels.hereditary_descendants
