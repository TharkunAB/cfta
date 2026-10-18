import MicroCFTA.SourceCurrentStoredRootDeletionErasure
namespace MicroCFTA.DeletionErasureKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open InternedStoredMuOrigins (Normal)
open InternedNestedProvenance (Values)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentNativeCallbackErasure (eraseSelf)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def source : Syntax Nat Bool := .binder false (.binder false (.var 1))
private def actual := build source [] empty
private def root : Value Nat Bool := match actual with | .done value _ => value | .pending .. => .empty
private def reader := actual.state
private def hidden : Value Nat Bool := match root with | .mu _ body _ _ => body | _ => .empty
private def own : Reference := match root with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def assignment : Reference → Profile := fun name => some [name]
private def inputs : List (Value Nat Bool) := [.reference own,hidden,.reference own,.empty]
private def combined := run (InternedConstructorTemplates.makeUnion inputs) reader
private def erased := eraseSelf own (run (withoutSelfReference own combined.1) combined.2).1
private def bareErased := eraseSelf own (run (withoutSelfReference own (.reference own : Value Nat Bool)) reader).1
private theorem actual_done : build source [] empty = .done root reader := by cbv
private theorem normal : Normal reader := by
  simpa only [actual_done,InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryNormal.closed_normal source
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result root reader actual_done
private theorem hidden_available : Available reader hidden := root_available.children hidden (by cbv; exact List.mem_cons_self)
private theorem own_available : Available reader (.reference own) := hidden_available.children (.reference own) (by cbv; exact List.mem_cons_self)
private theorem input_values : Values reader inputs := by
  intro value member
  change value ∈ [.reference own,hidden,.reference own,.empty] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact own_available
  · exact hidden_available
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
private theorem erased_profile : Equivalent (deleted (fun _ => false) erased assignment) (some [own]) := by
  have equation := SourceCurrentStoredRootDeletionErasure.erased_filter (fun _ => false) own combined.1 assignment
    combined.2 combined_normal combined_available
  have observed : deleted (fun name => false || (name == own)) combined.1 assignment = some [own] := by cbv
  rw [observed] at equation
  exact equation
private theorem standalone : Equivalent (deleted (fun _ => false) bareErased assignment)
    (deleted (fun name => false || (name == own)) (.reference own : Value Nat Bool) assignment) :=
  SourceCurrentStoredRootDeletionErasure.erased_filter (fun _ => false) own (.reference own) assignment reader normal own_available
private theorem checked_witness :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧ root.free = [] ∧
    Available reader hidden ∧ hidden.free = [own] ∧
    (∃ entry stored depth ordinary, hidden = .mu entry stored depth ordinary ∧ stored = .reference own) ∧
    denote hidden assignment = some [own] ∧ erased = hidden ∧
    Equivalent (deleted (fun _ => false) erased assignment) (some [own]) ∧ bareErased = .empty ∧
    Equivalent (deleted (fun _ => false) bareErased assignment)
      (deleted (fun name => false || (name == own)) (.reference own : Value Nat Bool) assignment) := by
  refine ⟨actual_done,normal,root_available,(by cbv),hidden_available,(by cbv),?_,(by cbv),
    (by cbv),erased_profile,(by cbv),standalone⟩
  exact ⟨_,_,_,_,(by cbv),(by cbv)⟩

theorem actual_hidden_mu_and_bare_erasure :
    build source [] empty = .done root reader ∧ Normal reader ∧ Available reader root ∧ root.free = [] ∧
    Available reader hidden ∧ hidden.free = [own] ∧
    (∃ entry stored depth ordinary, hidden = .mu entry stored depth ordinary ∧ stored = .reference own) ∧
    denote hidden assignment = some [own] ∧ erased = hidden ∧
    Equivalent (deleted (fun _ => false) erased assignment) (some [own]) ∧ bareErased = .empty ∧
    Equivalent (deleted (fun _ => false) bareErased assignment)
      (deleted (fun name => false || (name == own)) (.reference own : Value Nat Bool) assignment) := checked_witness
end MicroCFTA.DeletionErasureKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.DeletionErasureKernels.actual_hidden_mu_and_bare_erasure
#print MicroCFTA.DeletionErasureKernels.actual_hidden_mu_and_bare_erasure
#print axioms MicroCFTA.DeletionErasureKernels.actual_hidden_mu_and_bare_erasure
