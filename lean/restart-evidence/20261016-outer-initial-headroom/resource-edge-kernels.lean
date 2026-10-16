import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ResourceEdgeKernels
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove edgeRank)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem constructed_edge_with_final_capacity (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before) (rows arity bound : Nat) (limits : Limits)
    (profile : EdgeShape rows arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits request.value)
    (heightBound : MergedOrdinaryHeight.edgeHeight request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before) result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧ Post formulas solver next before after final ∧
        EdgeResident after.checked.native.machine.heap result ∧ Stored after ∧ EdgeNarrow request.value result ∧
        EdgeCertificate request result ∧ EdgeLaw formulas solver request result ∧
        ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
          nodeRequests requests ≤ nodeBudget limits rows arity bound ∧ edgeRequests requests ≤ edgeBudget limits rows arity bound ∧
          SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after.checked := by
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, narrow, certificate, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge.finite bits formulas solver budget request initial inherited resident domain
      stored active rows arity bound limits profile guards heightBound room
  obtain ⟨requests, work, nodes, edges⟩ := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.edge_call formulas solver reads
    inventory initial inherited resident domain stored rows arity bound limits profile guards heightBound
  have supplies := work.next_le
  have capacity : SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after.checked := by
    rcases room with ⟨nodeRoom, edgeRoom⟩
    constructor <;> omega
  exact ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, narrow, certificate, law,
    requests, work, nodes, edges, capacity⟩

#print axioms constructed_edge_with_final_capacity
#check @constructed_edge_with_final_capacity

end MicroCFTA.ResourceEdgeKernels
