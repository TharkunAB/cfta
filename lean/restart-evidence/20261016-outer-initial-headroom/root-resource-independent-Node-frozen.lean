import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceRows
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterActual

/-!
# Ordinary outer execution from initial constructor headroom

Strong node-rank induction constructs every smaller call.
Parent and descendant Work preserve the reserved suffix supply.
The theorem assumes initial profiles and capacities.
It assumes no future entry plan or completed outer graph.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceNode
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (NodeResult Below)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open MergedOrdinaryHeight (height edgesHeight)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem body
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request - 1) before)
    (ih : Below bits formulas solver budget (nodeRank request))
    (rowLimit arity bound : Nat) (limits : Limits) (profile : NodeShape rowLimit arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits request.value)
    (heightBound : height request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (nodeNodes rowLimit arity limits bound) (nodeEdges rowLimit arity limits bound)) :
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
          cases bound with
          | zero => simp only [height] at heightBound; omega
          | succ bound =>
              have rowsHeight : edgesHeight edges ≤ bound := Nat.le_of_add_le_add_right heightBound
              have rowsRoom : Headroom bits before.checked.native.machine.heap
                  (edges.length * rowNodes rowLimit arity limits bound)
                  (edges.length * rowEdges rowLimit arity limits bound) := by
                apply room.mono
                · have enough := Nat.mul_le_mul_right (rowNodes rowLimit arity limits bound) profile.1
                  change edges.length * rowNodes rowLimit arity limits bound ≤ 1 + rowLimit * rowNodes rowLimit arity limits bound
                  omega
                · exact Nat.mul_le_mul_right (rowEdges rowLimit arity limits bound) profile.1
              obtain ⟨results, middle, _rowInventory, final, rows, reads, checks, rowPost, _resident, _rowStored, _rowBounds⟩ :=
                SourceCurrentAllocatedFiniteOrdinaryOuterResourceRows.rows formulas solver budget
                  (nodeRank ⟨inheritedValue, .node entry edges depth free⟩) inheritedValue edges initial inherited resident rowsDomain
                  (fun edge member => SourceCurrentAllocatedPartialActiveOrder.edge_lt_node inheritedValue entry edges depth free edge member)
                  stored active ih rowLimit arity bound limits profile.2 guards rowsHeight rowsRoom
              let actual := NodeBody.ordinary (entry := entry) (depth := depth) (free := free) rows
              have actualReads : NodeBodyReads formulas solver actual memos final := .ordinary reads
              have actualChecks := SourceCurrentAllocatedPartialChecksComposition.ordinary
                (entry := entry) (depth := depth) (free := free) rows checks
              obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_body formulas solver
                actualReads inventory actualChecks initial inherited available
              have produced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.node_body formulas solver
                actualReads inventory initial inherited available (.ordinary rowsDomain) stored
              exact ⟨_, _, next, final, actual, actualReads, actualChecks, post, output, produced.1, produced.2.1, law⟩

private theorem step
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before)
    (ih : Below bits formulas solver budget (nodeRank request))
    (rowLimit arity bound : Nat) (limits : Limits) (profile : NodeShape rowLimit arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits request.value)
    (heightBound : height request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (nodeNodes rowLimit arity limits bound) (nodeEdges rowLimit arity limits bound)) :
    NodeResult bits formulas solver budget request before memos := by
  have safe := SourceCurrentAllocatedPartialActiveOrder.node_begin_safe formulas solver request before
    initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent available active
  rcases safe with ⟨result, ready⟩ | ⟨owner, start⟩
  · have started : beginNode request before =
        ((beginNode request before).1, .ready result, (beginNode request before).2.2) := Prod.ext rfl (Prod.ext ready rfl)
    obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver
      initial inherited available started
    obtain ⟨same, narrowed⟩ := stored.structural.node_ready formulas solver request (beginNode request before).2.2
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
    have ownerIH : Below bits formulas solver budget (nodeRank owner) := by rw [rankSame]; exact ih
    have ownerRoom : Headroom bits (beginNode request before).2.2.checked.native.machine.heap
        (nodeNodes rowLimit arity limits bound) (nodeEdges rowLimit arity limits bound) := by
      have components := beginNode_components request before
      simpa only [components.1] using room
    obtain ⟨result, middle, next, final, actualBody, reads, checks, bodyPost, bodyOutput, _bodyStored, _narrowed, bodyLaw⟩ :=
      body formulas solver budget owner runningContext good.inherited good.input ownerDomain
        (stored.beginNode request) ownerActive ownerIH
        rowLimit arity bound limits (by simpa only [same] using profile)
        (by simpa only [same] using guards) (by simpa only [same] using heightBound) ownerRoom
    obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_finish formulas solver
      initial inherited available started actualBody bodyPost bodyOutput bodyLaw
    let actual := NodeCall.evaluate started actualBody
    have actualReads : NodeCallReads formulas solver actual memos final := .evaluate (started := started) reads
    have produced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.node_call formulas solver actualReads
      inventory initial inherited available domain stored
    exact ⟨result, _, next, final, actual, actualReads,
      SourceCurrentAllocatedPartialChecksComposition.node_evaluate started actualBody checks,
      post, output, produced.1, produced.2.1, law⟩

/-- Initial profiles and constructor headroom construct finite literal ordinary node execution. -/
theorem finite
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before)
    (rowLimit arity bound : Nat) (limits : Limits) (profile : NodeShape rowLimit arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits request.value)
    (heightBound : height request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (nodeNodes rowLimit arity limits bound) (nodeEdges rowLimit arity limits bound)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ NodeNarrow request.value result ∧ NodeLaw formulas solver request result := by
  have completed : ∀ rank, Below bits formulas solver budget rank := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro inventory before memos candidate lower context ready input domain stored active rows arity bound limits profile guards heightBound room
        exact step formulas solver budget candidate context ready input domain stored active (ih (nodeRank candidate) lower)
          rows arity bound limits profile guards heightBound room
  obtain ⟨result, after, next, final, actual, reads, checks, post, output, retained, narrowed, law⟩ :=
    completed (nodeRank request + 1) request (Nat.lt_succ_self _) initial inherited available domain stored active
      rowLimit arity bound limits profile guards heightBound room
  exact ⟨result, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.nodeCall_complete actual,
    actual, reads, checks, post, output, retained, narrowed, law⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceNode
