import MicroCFTA.SourceCurrentStoredRootDeletionConstruction
namespace MicroCFTA.DeletionConstructionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open InternedStoredMuOrigins (Normal)
open InternedNestedProvenance (Values)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredRootDeletion (deleted deletedMany)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def source : Syntax Nat Bool := .binder false (.node [.mk 7 false [.binder false (.var 1)]])
private def actual := build source [] empty
private def root : Value Nat Bool := match actual with | .done value _ => value | .pending .. => .empty
private def reader := actual.state
private def body := match root with | .mu _ body _ _ => body | _ => .empty
private def own : Reference := match root with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def row : EdgeValue Nat Bool := match nodeEdges body with
  | row :: _ => row | _ => .mk ⟨0,⟨7,[],false⟩⟩ []
private def inner : Value Nat Bool := row.children.getD 0 .empty
private def assignment : Reference → Profile := fun name => some [name]
private def cuts : Reference → Bool := fun name => name == own
private def inputs : List (Value Nat Bool) := [.reference own,inner,.reference own,.empty]
private def combined := run (InternedConstructorTemplates.makeUnion inputs) reader
private def normalized := run (InternedConstructorTemplates.makeNode [row,row]) reader
private def filtered := run (withoutSelfReference own combined.1) combined.2
private theorem actual_done : build source [] empty = .done root reader := by cbv
private theorem normal : Normal reader := by
  simpa only [actual_done,InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryNormal.closed_normal source
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result root reader actual_done
private theorem body_available : Available reader body := root_available.children body (by cbv; exact List.mem_cons_self)
private theorem inner_available : Available reader inner := body_available.children inner (by cbv; exact List.mem_cons_self)
private theorem own_available : Available reader (.reference own) := inner_available.children (.reference own) (by cbv; exact List.mem_cons_self)
private theorem row_resident : EdgeResident reader row :=
  (resident_edges reader normal.facts.linked body body_available.resident) row (by cbv; exact List.mem_cons_self)
private theorem input_values : Values reader inputs := by
  intro value member
  change value ∈ [.reference own,inner,.reference own,.empty] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact own_available
  · exact inner_available
  · exact own_available
  · exact empty_available reader
private theorem combined_normal : Normal combined.2 :=
  ⟨(InternedNestedFacts.union_verified inputs reader normal.facts input_values).facts,
    InternedLiveEdges.makeUnion_live inputs reader normal.live,
    InternedUnionNormalForm.makeUnion_flat inputs reader normal.flat input_values,
    InternedNonemptyRecords.makeUnion_nonempty inputs reader normal.proper,
    InternedUnionNonemptyMembers.makeUnion_membersNonempty inputs reader normal.members input_values⟩
private theorem combined_available : Available combined.2 combined.1 :=
  (InternedProbeProvenance.makeUnion_available inputs reader normal.facts.coherent normal.facts.cached input_values).2.2
private theorem input_profile : deletedMany cuts inputs assignment = some [own] := by cbv
private theorem combined_profile : Equivalent (deleted cuts combined.1 assignment) (some [own]) := by
  have equation := SourceCurrentStoredRootDeletionConstruction.makeUnion cuts inputs assignment reader normal input_values
  rw [input_profile] at equation
  exact equation
private theorem node_profile : deleted cuts normalized.1 assignment = none := by
  have equation := SourceCurrentStoredRootDeletionConstruction.makeNode cuts [row,row] assignment reader normal
    (by intro selected member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> exact row_resident)
  change deleted cuts normalized.1 assignment = _ at equation
  rw [equation]
  cbv
private theorem filter_profile : Equivalent (denote filtered.1 assignment) (some [own]) := by
  have equation := SourceCurrentStoredRootDeletionConstruction.filter_profile own combined.1 assignment combined.2 combined_normal combined_available
  have noBare : (combined.1.referenceOf == .ref own) = false := by cbv
  rw [noBare] at equation
  simp only [Bool.false_eq_true,ite_false] at equation
  exact InternedProfileEquivalence.trans equation combined_profile
private theorem checked_witness :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧ root.free = [] ∧
    Available reader inner ∧ inner.free = [own] ∧
    (∃ entry stored depth ordinary, inner = .mu entry stored depth ordinary ∧ stored = .reference own) ∧
    denote inner assignment = some [own] ∧ deleted cuts (.reference own : Value Nat Bool) assignment = some [] ∧
    Values reader inputs ∧ Normal combined.2 ∧ Available combined.2 combined.1 ∧
    Equivalent (deleted cuts combined.1 assignment) (some [own]) ∧ filtered.1 = inner ∧
    Equivalent (denote filtered.1 assignment) (some [own]) ∧
    (run (withoutSelfReference own (.reference own : Value Nat Bool)) reader).1 = .reference own ∧
    EdgeResident reader row ∧ (nodeEdges normalized.1).length = 1 ∧ deleted cuts normalized.1 assignment = none := by
  refine ⟨actual_done,normal,root_available,(by cbv),inner_available,(by cbv),?_,
    (by cbv),(by cbv),input_values,combined_normal,combined_available,combined_profile,(by cbv),filter_profile,
    (by rfl),row_resident,(by cbv),node_profile⟩
  exact ⟨_,_,_,_,(by cbv),(by cbv)⟩

theorem original_reference_and_hidden_mu :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧ root.free = [] ∧
    Available reader inner ∧ inner.free = [own] ∧
    (∃ entry stored depth ordinary, inner = .mu entry stored depth ordinary ∧ stored = .reference own) ∧
    denote inner assignment = some [own] ∧ deleted cuts (.reference own : Value Nat Bool) assignment = some [] ∧
    Values reader inputs ∧ Normal combined.2 ∧ Available combined.2 combined.1 ∧
    Equivalent (deleted cuts combined.1 assignment) (some [own]) ∧ filtered.1 = inner ∧
    Equivalent (denote filtered.1 assignment) (some [own]) ∧
    (run (withoutSelfReference own (.reference own : Value Nat Bool)) reader).1 = .reference own ∧
    EdgeResident reader row ∧ (nodeEdges normalized.1).length = 1 ∧ deleted cuts normalized.1 assignment = none := checked_witness
end MicroCFTA.DeletionConstructionKernels
