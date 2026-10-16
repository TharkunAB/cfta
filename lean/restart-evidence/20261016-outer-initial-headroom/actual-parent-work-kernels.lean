import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualParentWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ActualParentWorkKernels
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialSourceReads (EdgeBodyReads)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests nodeReservations edgeReservations)
open MergedOrdinaryHeight (edgeHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GuardEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem exact_parent_work_profile_and_counters (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {width budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : EdgeValue Symbol Guard}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (stored : Stored before)
    (limits : Limits) (rows arity bound : Nat) (guards : GuardEdge limits request.value)
    (profile : EdgeShape rows arity request.value) (heightBound : edgeHeight request.value ≤ bound) :
    Stored after ∧ EdgeCertificate request result ∧ ∃ next, Post formulas solver next before after final ∧
      ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ nodeBudget limits rows arity bound ∧ edgeRequests requests ≤ edgeBudget limits rows arity bound ∧
        after.checked.native.machine.heap.nodes.next = before.checked.native.machine.heap.nodes.next + nodeReservations requests ∧
        after.checked.native.machine.heap.edges.next = before.checked.native.machine.heap.edges.next + edgeReservations requests ∧
        after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + nodeBudget limits rows arity bound ∧
        after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edgeBudget limits rows arity bound := by
  obtain ⟨requests, trace, nodes, edges⟩ := SourceCurrentAllocatedFiniteOrdinaryActualParentWork.edge_body
    formulas solver reads inventory initial inherited resident stored limits rows arity bound guards profile heightBound
  have domain := EdgeShape.domain request.value profile
  obtain ⟨retained, _narrow, certificate⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_body
    formulas solver reads inventory initial inherited resident domain stored
  obtain ⟨_checks, next, post, _resident, _stored, _narrow, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver reads inventory initial inherited resident domain stored.structural
  have exactCounts := trace.next_exact
  have supplies := trace.next_le
  exact ⟨retained, certificate, next, post, requests, trace, nodes, edges, exactCounts.1, exactCounts.2, by omega, by omega⟩

#print axioms exact_parent_work_profile_and_counters
#check @exact_parent_work_profile_and_counters

end MicroCFTA.ActualParentWorkKernels
