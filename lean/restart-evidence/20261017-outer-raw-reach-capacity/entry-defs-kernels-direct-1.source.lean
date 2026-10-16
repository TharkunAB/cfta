import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ResourceEntryKernels
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState (NodeRequest EdgeRequest)
open SourceCurrentAllocatedPartialGraph (NodeCall EdgeBody)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads EdgeBodyReads)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs (Admitted)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate EdgeCertificate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem supplied_parent_has_own_reads {bits budget : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {request : EdgeRequest} {before after : Caller (bits + 2)} {result : EdgeValue Symbol Guard}
    (actual : EdgeBody budget request before result after)
    (admitted : Admitted bits formulas solver (.edgeBody request before)) :
    ∃ (memos final : Memos), EdgeBodyReads formulas solver actual memos final ∧
      ∃ next, Post formulas solver next before after final ∧ Stored after ∧ EdgeCertificate request result := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs.edge_body_capacity (budget := budget) admitted
  obtain ⟨inventory, memos, rows, arity, bound, limits, initial, stored, inherited,
    resident, domain, _profile, _guards, _height, _room, _active⟩ := admitted
  obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterParentReads.edge_body bits formulas solver actual
    inventory initial inherited resident domain stored.structural capacity
  obtain ⟨_checks, next, post, _resident, _stored, _narrow, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver reads inventory initial inherited
      resident domain stored.structural
  obtain ⟨retained, _narrow, quantitative⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_body formulas solver
    reads inventory initial inherited resident domain stored
  exact ⟨memos, final, reads, next, post, retained, quantitative⟩

theorem admitted_node_constructs_own_run {bits : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (request : NodeRequest) (before : Caller (bits + 2))
    (admitted : Admitted bits formulas solver (.nodeCall request before)) :
    ∃ (memos : Memos) result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Stored after ∧ NodeCertificate request result := by
  obtain ⟨inventory, memos, rows, arity, bound, limits, initial, stored, inherited,
    available, domain, profile, guards, heightBound, room, active⟩ := admitted
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, _available,
    retained, _narrow, quantitative, _work, _room, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot.finite bits formulas solver budget request initial inherited
      available domain stored active rows arity bound limits profile guards heightBound room
  exact ⟨memos, result, after, next, final, stable, actual, reads, checks, post, retained, quantitative⟩

#print axioms supplied_parent_has_own_reads
#check @supplied_parent_has_own_reads
#print axioms admitted_node_constructs_own_run
#check @admitted_node_constructs_own_run

end MicroCFTA.ResourceEntryKernels
