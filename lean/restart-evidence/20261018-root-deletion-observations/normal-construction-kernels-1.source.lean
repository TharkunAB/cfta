import MicroCFTA.SourceCurrentStoredProfileNormalConstruction
namespace MicroCFTA.NormalConstructionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile)
open InternedStoredMuOrigins (Normal)
open SourceCurrentStoredProfileFunction (denote)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def source : Syntax Nat Bool := .binder false (.node [.mk 7 false [.var 0]])
private def actual := build source [] empty
private def root : Value Nat Bool := match actual with | .done value _ => value | .pending .. => .empty
private def reader := actual.state
private def body := match root with | .mu _ body _ _ => body | _ => .empty
private def row : EdgeValue Nat Bool := match nodeEdges body with
  | row :: _ => row | _ => .mk ⟨0,⟨7,[],false⟩⟩ []
private def assignment : Reference → Profile := fun _ => some []
private def normalized := run (InternedConstructorTemplates.makeNode [row,row]) reader
private theorem actual_done : build source [] empty = .done root reader := by cbv
private theorem normal : Normal reader := by
  simpa only [actual_done,InternedNestedConstruction.Outcome.state] using
    InternedFreshOrdinaryNormal.closed_normal source
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result root reader actual_done
private theorem body_available : Available reader body :=
  root_available.children body (by cbv; exact List.mem_cons_self)
private theorem row_resident : EdgeResident reader row :=
  (resident_edges reader normal.facts.linked body body_available.resident)
    row (by cbv; exact List.mem_cons_self)
private theorem profile_empty : denote normalized.1 assignment = some [] := by
  have equation := SourceCurrentStoredProfileNormalConstruction.makeNode [row,row] assignment reader normal
    (by intro selected member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> exact row_resident)
  change denote normalized.1 assignment = _ at equation
  rw [equation]
  cbv
private theorem checked_witness :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧
    root.free = [] ∧ (∃ entry stored depth ordinary, root = .mu entry stored depth ordinary ∧
      .interned entry.identity ∈ stored.free) ∧
    Available reader body ∧ body.free ≠ [] ∧ EdgeResident reader row ∧
    (nodeEdges normalized.1).length = 1 ∧ normalized.1.referenceOf ≠ .empty ∧
    denote normalized.1 assignment = some [] := by
  refine ⟨actual_done,normal,root_available,(by cbv),?_,body_available,
    (by cbv; intro impossible; cases impossible),row_resident,(by cbv),
    (by cbv; intro impossible; cases impossible),profile_empty⟩
  refine ⟨_,_,_,_,(by cbv),?_⟩
  cbv
  exact List.mem_cons_self

theorem actual_normal_constructor :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧
    root.free = [] ∧ (∃ entry stored depth ordinary, root = .mu entry stored depth ordinary ∧
      .interned entry.identity ∈ stored.free) ∧
    Available reader body ∧ body.free ≠ [] ∧ EdgeResident reader row ∧
    (nodeEdges normalized.1).length = 1 ∧ normalized.1.referenceOf ≠ .empty ∧
    denote normalized.1 assignment = some [] := checked_witness
end MicroCFTA.NormalConstructionKernels
