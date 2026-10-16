import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.UniformCapacityKernels
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
open MergedOrdinaryHeight (edgeHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GuardEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem supplied_parent_admitted (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before after : Caller (bits + 2)} {result : EdgeValue Symbol Guard}
    (actual : EdgeBody budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (stored : Stored before)
    (limits : Limits) (rows arity bound : Nat) (guards : GuardEdge limits request.value)
    (profile : EdgeShape rows arity request.value) (heightBound : edgeHeight request.value ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget limits rows arity bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget limits rows arity bound ≤ 2 ^ (bits + 2)) :
    ∃ final, EdgeBodyReads formulas solver actual memos final ∧
      ∃ next, Post formulas solver next before after final ∧ Stored after ∧ EdgeCertificate request result := by
  obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryParentUniformCapacity.edge_body_reads
    bits formulas solver actual inventory initial inherited resident stored limits rows arity bound guards profile heightBound nodes edges
  have domain := EdgeShape.domain request.value profile
  obtain ⟨_checks, next, post, _resident, _stored, _narrow, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver reads inventory initial inherited resident domain stored.structural
  obtain ⟨retained, _narrow, certificate⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_body
    formulas solver reads inventory initial inherited resident domain stored
  exact ⟨final, reads, next, post, retained, certificate⟩

theorem raw_rejection_needs_no_headroom {bits budget : Nat} (request : EdgeRequest) (before : Caller (bits + 2))
    (rejected : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = true) :
    SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget request before := by
  intro live
  cases live.symm.trans rejected

#print axioms supplied_parent_admitted
#check @supplied_parent_admitted
#print axioms raw_rejection_needs_no_headroom
#check @raw_rejection_needs_no_headroom

end MicroCFTA.UniformCapacityKernels
