import MicroCFTA.SourceCurrentAllocatedPartialConditionalStoreTrace
import MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainNode

/-!
# Finite plain continuation after an actual mixed outer prefix

A completed prefix supplies its own strict reads and checks. Its actual
return retains conditional stores and filtered active-owner bounds.
The next plain node call constructs its own execution at that return.
Its full Post composes with the earlier prefix. These theorems do not
assert completion of an arbitrary first constrained call.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalContinuation
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove)
open SourceCurrentAllocatedPartialActiveOrder (nodeRank)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- The exact completed node prefix constructs its own finite plain continuation and composed receipt. -/
theorem after_node (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before middle : Caller width} {memos middleMemos : Memos}
    {earlierBudget : Nat} {earlier : NodeRequest} {earlierResult : Node}
    {prefix : NodeCall earlierBudget earlier before earlierResult middle}
    (reads : NodeCallReads formulas solver prefix memos middleMemos) (checks : Checks (nodeCallTrace prefix))
    (initial : Context formulas solver inventory before memos)
    (earlierReady : EqReady before.checked.operations.constraints earlier.inherited)
    (earlierInput : Available before.checked.native.machine.heap earlier.value)
    (stored : Stored before) (budget : Nat) (request : NodeRequest)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (region : SourceEqualityPartialPlainRegion.Region request.value)
    (active : ActiveAbove (nodeRank request) before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall
          f g s r e p h m c n budget request middle) result after ∧
      ∃ actual : NodeCall budget request middle result after,
        NodeCallReads formulas solver actual middleMemos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  obtain ⟨_currentInventory, prefixPost, _prefixOutput, _prefixLaw⟩ :=
    SourceCurrentAllocatedPartialActual.node_call formulas solver reads inventory checks initial earlierReady earlierInput
  have currentStored := SourceCurrentAllocatedPartialConditionalStoreTrace.node_call formulas solver
    reads checks initial earlierReady earlierInput stored
  have currentActive := SourceCurrentAllocatedPartialConditionalFrames.node_call prefix active
  obtain ⟨result, after, next, final, stable, actual, actualReads, actualChecks, post, output, retained, law⟩ :=
    SourceCurrentAllocatedPartialConditionalPlainNode.finite formulas solver budget request prefixPost.context
      (inherited.grows prefixPost.effects.grows.constraint_growth)
      (prefixPost.effects.keeps.available _ available) region currentStored currentActive
  exact ⟨result, after, next, final, stable, actual, actualReads, actualChecks,
    prefixPost.trans post, output, retained, law⟩

/-- The exact completed edge prefix constructs its own finite plain continuation and composed receipt. -/
theorem after_edge (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before middle : Caller width} {memos middleMemos : Memos}
    {earlierBudget : Nat} {earlier : EdgeRequest} {earlierResult : Edge}
    {prefix : EdgeCall earlierBudget earlier before earlierResult middle}
    (reads : EdgeCallReads formulas solver prefix memos middleMemos) (checks : Checks (edgeCallTrace prefix))
    (initial : Context formulas solver inventory before memos)
    (earlierReady : EqReady before.checked.operations.constraints earlier.inherited)
    (earlierInput : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap earlier.value)
    (stored : Stored before) (budget : Nat) (request : NodeRequest)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (region : SourceEqualityPartialPlainRegion.Region request.value)
    (active : ActiveAbove (nodeRank request) before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall
          f g s r e p h m c n budget request middle) result after ∧
      ∃ actual : NodeCall budget request middle result after,
        NodeCallReads formulas solver actual middleMemos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  obtain ⟨_currentInventory, prefixPost, _prefixOutput, _prefixLaw⟩ :=
    SourceCurrentAllocatedPartialActual.edge_call formulas solver reads inventory checks initial earlierReady earlierInput
  have currentStored := SourceCurrentAllocatedPartialConditionalStoreTrace.edge_call formulas solver
    reads checks initial earlierReady earlierInput stored
  have currentActive := SourceCurrentAllocatedPartialConditionalFrames.edge_call prefix active
  obtain ⟨result, after, next, final, stable, actual, actualReads, actualChecks, post, output, retained, law⟩ :=
    SourceCurrentAllocatedPartialConditionalPlainNode.finite formulas solver budget request prefixPost.context
      (inherited.grows prefixPost.effects.grows.constraint_growth)
      (prefixPost.effects.keeps.available _ available) region currentStored currentActive
  exact ⟨result, after, next, final, stable, actual, actualReads, actualChecks,
    prefixPost.trans post, output, retained, law⟩

end MicroCFTA.SourceCurrentAllocatedPartialConditionalContinuation
