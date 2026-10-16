import MicroCFTA.SourceCurrentAllocatedPartialPlainRows
import MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal

/-!
# Finite current node execution in the plain Region

Strong induction on node rank discharges every smaller recursive call.
Finite row and child loops retain the actual returned state at each prefix.
Warm hits use their stored owners. No successful execution, future graph,
range plan, or recursive completion callback is a public premise.
This theorem covers one pass in Region. General constraints remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialPlainNode
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialPlainRecursionDefs (NodeResult Below)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Region" => SourceEqualityPartialPlainRegion.Region
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem body
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (region : Region request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request - 1) before)
    (ih : Below (width := width) formulas solver budget (nodeRank request)) :
    ∃ result after next final, ∃ actual : NodeBody budget request before result after,
      NodeBodyReads formulas solver actual memos final ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      Stored after ∧ NodeLaw formulas solver request result := by
  by_cases terminal : SourceCurrentAllocatedPartialPlainTerminal.Terminal request.value
  · obtain ⟨result, actual, reads, checks, post, output, retained, law, _done⟩ :=
      SourceCurrentAllocatedPartialPlainTerminal.complete formulas solver budget request initial inheritedReady available stored terminal
    exact ⟨result, before, inventory, memos, actual, reads, checks, post, output, retained, law⟩
  · cases request with
    | mk inherited value =>
      cases region with
      | empty => exact False.elim (terminal .empty)
      | binder => exact False.elim (terminal .binder)
      | union => exact False.elim (terminal .union)
      | @ordinary edges entry depth free regions =>
          have resident := InternedEdgeResidency.resident_edges _
            initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
          obtain ⟨results, middle, rowInventory, final, rows, reads, checks, rowPost, _resident, rowStored⟩ :=
            SourceCurrentAllocatedPartialPlainRows.rows formulas solver budget (nodeRank ⟨inherited, .node entry edges depth free⟩)
              inherited edges initial inheritedReady resident regions
              (fun edge member => SourceCurrentAllocatedPartialActiveOrder.edge_lt_node inherited entry edges depth free edge member)
              stored active ih
          let actual := NodeBody.ordinary (entry := entry) (depth := depth) (free := free) rows
          have actualReads : NodeBodyReads formulas solver actual memos final := .ordinary reads
          have actualChecks := SourceCurrentAllocatedPartialChecksComposition.ordinary
            (entry := entry) (depth := depth) (free := free) rows checks
          obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_body formulas solver
            actualReads inventory actualChecks initial inheritedReady available
          exact ⟨_, _, next, final, actual, actualReads, actualChecks, post, output,
            rowStored.advance _ middle.fourth middle.merge, law⟩

private theorem step
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (region : Region request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before)
    (ih : Below (width := width) formulas solver budget (nodeRank request)) : NodeResult formulas solver budget request before memos := by
  have safe := SourceCurrentAllocatedPartialActiveOrder.node_begin_safe formulas solver request before
    initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent available active
  rcases safe with ⟨result, ready⟩ | ⟨owner, start⟩
  · have started : beginNode request before =
        ((beginNode request before).1, .ready result, (beginNode request before).2.2) :=
      Prod.ext rfl (Prod.ext ready rfl)
    obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver
      initial inheritedReady available started
    exact ⟨result, _, inventory, memos, .hit started, .hit (started := started),
      SourceCurrentAllocatedPartialChecksComposition.node_hit started, post, output, stored.beginNode request, law⟩
  · have started : beginNode request before =
        ((beginNode request before).1, .evaluate owner, (beginNode request before).2.2) :=
      Prod.ext rfl (Prod.ext start rfl)
    obtain ⟨runningContext, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
      initial inheritedReady available started
    obtain ⟨same, ownerRegion⟩ := SourceCurrentAllocatedPartialPlainInputs.node_evaluate formulas solver request owner before
      (beginNode request before).2.2 (beginNode request before).1 initial.sound
      initial.ready.semantic.ready.semantic.1.normal.facts.coherent inheritedReady available region started
    have rankSame : nodeRank owner = nodeRank request := by simp only [nodeRank, same]
    have smaller : nodeRank request - 1 < nodeRank request := by simp only [nodeRank]; omega
    have runningActive := SourceCurrentAllocatedPartialActiveOrder.node_push formulas solver initial.sound
      initial.ready.semantic.ready.semantic.1.normal.facts.coherent inheritedReady available active smaller started
    have ownerActive : ActiveAbove (nodeRank owner - 1) (beginNode request before).2.2 := by
      simpa only [rankSame] using runningActive
    have ownerIH : Below (width := width) formulas solver budget (nodeRank owner) := by
      rw [rankSame]
      exact ih
    obtain ⟨result, middle, next, final, actualBody, reads, checks, bodyPost, bodyOutput, bodyStored, bodyLaw⟩ :=
      body formulas solver budget owner runningContext good.inherited good.input ownerRegion
        (stored.beginNode request) ownerActive ownerIH
    obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_finish formulas solver
      initial inheritedReady available started actualBody bodyPost bodyOutput bodyLaw
    exact ⟨result, _, next, final, .evaluate started actualBody, .evaluate (started := started) reads,
      SourceCurrentAllocatedPartialChecksComposition.node_evaluate started actualBody checks,
      post, output, bodyStored.finishNode _ result, law⟩

/-- Initial Region input constructs finite literal node execution and its own complete receipt. -/
theorem finite
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (region : Region request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ NodeLaw formulas solver request result := by
  have completed : ∀ rank, Below (width := width) formulas solver budget rank := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro inventory before memos candidate lower context ready input region stored active
        exact step formulas solver budget candidate context ready input region stored active (ih (nodeRank candidate) lower)
  obtain ⟨result, after, next, final, actual, reads, checks, post, output, retained, law⟩ :=
    completed (nodeRank request + 1) request (Nat.lt_succ_self _) initial inheritedReady available region stored active
  exact ⟨result, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.nodeCall_complete actual,
    actual, reads, checks, post, output, retained, law⟩

end MicroCFTA.SourceCurrentAllocatedPartialPlainNode
