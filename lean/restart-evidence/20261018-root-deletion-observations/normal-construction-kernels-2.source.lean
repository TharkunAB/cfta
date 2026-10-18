import MicroCFTA.SourceCurrentStoredProfileNormalConstruction
namespace MicroCFTA.NormalConstructionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentStoredProfileFunction (denote)
open InternedStoredMuOrigins (Normal)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def source : Syntax Nat Bool := .binder false
  (.node [.mk 9 false [.node [.mk 7 false [.var 0]],.node [.mk 8 false []]]])
private def actual := build source [] empty
private def root : Value Nat Bool := match actual with | .done value _ => value | .pending .. => .empty
private def reader := actual.state
private def body := match root with | .mu _ body _ _ => body | _ => .empty
private def first : Value Nat Bool := ((nodeEdges body).flatMap EdgeValue.children).getD 0 .empty
private def second : Value Nat Bool := ((nodeEdges body).flatMap EdgeValue.children).getD 1 .empty
private def row : EdgeValue Nat Bool := match nodeEdges first with | row :: _ => row | _ => .mk ⟨0,⟨7,[],false⟩⟩ []
private def assignment : Reference → Profile := fun _ => some []
private def normalized := run (InternedConstructorTemplates.makeNode [row,row]) reader
private def merged := run (InternedConstructorTemplates.makeUnion [first,second,first,.empty]) reader
private theorem actual_done : build source [] empty = .done root reader := by cbv
private theorem normal : Normal reader := by
  simpa only [actual_done,InternedNestedConstruction.Outcome.state] using
    InternedFreshOrdinaryNormal.closed_normal source
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result root reader actual_done
private theorem body_available : Available reader body :=
  root_available.children body (by cbv; exact List.mem_cons_self)
private theorem first_available : Available reader first :=
  body_available.children first (by cbv; exact List.mem_cons_self)
private theorem second_available : Available reader second :=
  body_available.children second (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem row_resident : InternedEdgeResidency.EdgeResident reader row :=
  (InternedEdgeResidency.resident_edges reader normal.facts.linked first first_available.resident)
    row (by cbv; exact List.mem_cons_self)
private theorem first_empty : denote first assignment = some [] := by
  have equation := SourceCurrentStoredProfileComposition.node
    (match first with | .node entry _ _ _ => entry | _ => ⟨0,.node []⟩)
    (nodeEdges first) first.depth first.free assignment reader normal
  have shape : first = .node (match first with | .node entry _ _ _ => entry | _ => ⟨0,.node []⟩)
    (nodeEdges first) first.depth first.free := by cbv
  rw [←shape] at equation
  rw [equation first_available]
  cbv
private theorem second_opaque : denote second assignment = none := by
  rw [SourceCurrentStoredProfileFunction.closed second assignment (by cbv)]
  cbv
private theorem normalized_empty : denote normalized.1 assignment = some [] := by
  have equation := SourceCurrentStoredProfileNormalConstruction.makeNode [row,row] assignment reader normal
    (by intro selected member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> exact row_resident)
  change denote normalized.1 assignment = _ at equation
  rw [equation]
  cbv
private theorem merged_opaque : Equivalent (denote merged.1 assignment) none := by
  have equation := SourceCurrentStoredProfileNormalConstruction.makeUnion [first,second,first,.empty] assignment reader normal
    (by intro selected member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact first_available
        · exact second_available
        · exact first_available
        · exact empty_available reader)
  change Equivalent (denote merged.1 assignment) _ at equation
  simpa only [List.map_cons,List.map_nil,first_empty,second_opaque,SourceCurrentStoredProfileFunction.empty,
    InternedProfileSemantics.combineMany,InternedProfileSemantics.combine] using equation
private theorem checked_witness :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧
    root.free = [] ∧ (∃ entry stored depth ordinary, root = .mu entry stored depth ordinary ∧
      .interned entry.identity ∈ stored.free) ∧
    Available reader first ∧ Available reader second ∧ first.free ≠ [] ∧ second.free = [] ∧
    InternedEdgeResidency.EdgeResident reader row ∧
    (nodeEdges normalized.1).length = 1 ∧ normalized.1.referenceOf ≠ .empty ∧
    denote normalized.1 assignment = some [] ∧
    (nodeEdges merged.1).length = 2 ∧ Equivalent (denote merged.1 assignment) none := by
  refine ⟨actual_done,normal,root_available,(by cbv),?_,first_available,second_available,
    (by cbv; intro impossible; cases impossible),(by cbv),row_resident,(by cbv),
    (by cbv; intro impossible; cases impossible),normalized_empty,(by cbv),merged_opaque⟩
  refine ⟨_,_,_,_,(by cbv),?_⟩
  cbv
  exact List.mem_cons_self

theorem actual_normal_constructor :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧
    root.free = [] ∧ (∃ entry stored depth ordinary, root = .mu entry stored depth ordinary ∧
      .interned entry.identity ∈ stored.free) ∧
    Available reader first ∧ Available reader second ∧ first.free ≠ [] ∧ second.free = [] ∧
    InternedEdgeResidency.EdgeResident reader row ∧
    (nodeEdges normalized.1).length = 1 ∧ normalized.1.referenceOf ≠ .empty ∧
    denote normalized.1 assignment = some [] ∧
    (nodeEdges merged.1).length = 2 ∧ Equivalent (denote merged.1 assignment) none := checked_witness
end MicroCFTA.NormalConstructionKernels
