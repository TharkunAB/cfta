import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRows
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterActual

/-!
# Constructed constrained finite ordinary node recursion

Strong node-rank induction derives each smaller recursive call.
Each row recurses on the actual parent result and its height bound.
The entry plan checks machine ranges before the selected parent executes.
The proof constructs its own graph, reads, checks, and full return.
Quantitative machine capacity and general Mu progress remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNode
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs (NodeResult Below)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Plan" => SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem body
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request - 1) before)
    (ih : Below (width := width) formulas solver budget (nodeRank request))
    (plan : Plan budget (.nodeBody request before)) :
    ∃ result after next final, ∃ actual : NodeBody budget request before result after,
      NodeBodyReads formulas solver actual memos final ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      Stored after ∧ NodeNarrow request.value result ∧ NodeLaw formulas solver request result := by
  cases request with
  | mk inheritedValue value =>
      cases domain with
      | empty =>
          exact ⟨.empty, before, inventory, memos, .empty, .empty,
            SourceCurrentAllocatedPartialChecksComposition.empty, Post.refl initial, empty_available _,
            stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.node_refl .empty,
            SourceCurrentAllocatedPartialCallSteps.node_refl formulas solver _⟩
      | @ordinary edges entry depth free rowsDomain =>
          have resident := InternedEdgeResidency.resident_edges _
            initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
          obtain ⟨results, middle, rowInventory, final, rows, reads, checks, rowPost, _resident, _rowStored, _rowBounds⟩ :=
            SourceCurrentAllocatedFiniteOrdinaryOuterRows.rows formulas solver budget
              (nodeRank ⟨inheritedValue, .node entry edges depth free⟩) inheritedValue edges initial inherited resident rowsDomain
              (fun edge member => SourceCurrentAllocatedPartialActiveOrder.edge_lt_node inheritedValue entry edges depth free edge member)
              stored active ih (plan.restrict (.direct .node_ordinary))
          let actual := NodeBody.ordinary (entry := entry) (depth := depth) (free := free) rows
          have actualReads : NodeBodyReads formulas solver actual memos final := .ordinary reads
          have actualChecks := SourceCurrentAllocatedPartialChecksComposition.ordinary
            (entry := entry) (depth := depth) (free := free) rows checks
          obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_body formulas solver
            actualReads inventory actualChecks initial inherited available
          obtain ⟨retained, narrowed⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_body formulas solver
            actualReads inventory actualChecks initial inherited available (.ordinary rowsDomain) stored
          exact ⟨_, _, next, final, actual, actualReads, actualChecks, post, output, retained, narrowed, law⟩

private theorem step
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before)
    (ih : Below (width := width) formulas solver budget (nodeRank request))
    (plan : Plan budget (.nodeCall request before)) : NodeResult formulas solver budget request before memos := by
  have safe := SourceCurrentAllocatedPartialActiveOrder.node_begin_safe formulas solver request before
    initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent available active
  rcases safe with ⟨result, ready⟩ | ⟨owner, start⟩
  · have started : beginNode request before =
        ((beginNode request before).1, .ready result, (beginNode request before).2.2) := Prod.ext rfl (Prod.ext ready rfl)
    obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver
      initial inherited available started
    obtain ⟨same, narrowed⟩ := stored.node_ready formulas solver request (beginNode request before).2.2
      (beginNode request before).1 result initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent
      available domain started
    exact ⟨result, _, inventory, memos, .hit started, .hit (started := started),
      SourceCurrentAllocatedPartialChecksComposition.node_hit started, post, output, same.symm ▸ stored, narrowed, law⟩
  · have started : beginNode request before =
        ((beginNode request before).1, .evaluate owner, (beginNode request before).2.2) := Prod.ext rfl (Prod.ext start rfl)
    obtain ⟨runningContext, good, _key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
      initial inherited available started
    obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.node_evaluate formulas solver request owner before
      (beginNode request before).2.2 (beginNode request before).1 initial.sound
      initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available domain started
    have rankSame : nodeRank owner = nodeRank request := by simp only [nodeRank, same]
    have smaller : nodeRank request - 1 < nodeRank request := by simp only [nodeRank]; omega
    have runningActive := SourceCurrentAllocatedPartialActiveOrder.node_push formulas solver initial.sound
      initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available active smaller started
    have ownerActive : ActiveAbove (nodeRank owner - 1) (beginNode request before).2.2 := by
      simpa only [rankSame] using runningActive
    have ownerIH : Below (width := width) formulas solver budget (nodeRank owner) := by rw [rankSame]; exact ih
    obtain ⟨result, middle, next, final, actualBody, reads, checks, bodyPost, bodyOutput, bodyStored, narrowed, bodyLaw⟩ :=
      body formulas solver budget owner runningContext good.inherited good.input ownerDomain
        (stored.beginNode request) ownerActive ownerIH
        (plan.restrict (.direct (.node_evaluate started)))
    obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_finish formulas solver
      initial inherited available started actualBody bodyPost bodyOutput bodyLaw
    have frame := SourceCurrentAllocatedPartialFrames.node_body actualBody
      (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
    have retained := bodyStored.finishNode result (frame.node_running _ owner cell) (fun _ => narrowed)
    exact ⟨result, _, next, final, .evaluate started actualBody, .evaluate (started := started) reads,
      SourceCurrentAllocatedPartialChecksComposition.node_evaluate started actualBody checks,
      post, output, retained, by simpa only [same] using narrowed, law⟩

/-- Initial domain, causal tables, and entry word checks construct finite literal recursive node execution. -/
theorem finite
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before)
    (plan : Plan budget (.nodeCall request before)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ NodeNarrow request.value result ∧ NodeLaw formulas solver request result := by
  have completed : ∀ rank, Below (width := width) formulas solver budget rank := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro inventory before memos candidate lower context ready input domain stored active plan
        exact step formulas solver budget candidate context ready input domain stored active (ih (nodeRank candidate) lower) plan
  obtain ⟨result, after, next, final, actual, reads, checks, post, output, retained, narrowed, law⟩ :=
    completed (nodeRank request + 1) request (Nat.lt_succ_self _) initial inherited available domain stored active plan
  exact ⟨result, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.nodeCall_complete actual,
    actual, reads, checks, post, output, retained, narrowed, law⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNode
