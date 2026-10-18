import MicroCFTA.SourceCurrentGeneratedUnionPreparation
namespace MicroCFTA.UnionPreparationKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentGeneratedUnionPreparation (FilteredCalls)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol true []]
private def child : Syntax Nat Bool := .union [.var 0,leaf 0,leaf 1]
private def body : Syntax Nat Bool := .union [child,leaf 2]
private def source : Syntax Nat Bool := .binder false body
private def built := build source [] empty
private def root := val built
private def reader := built.state
private def raw := val (build body [.reference .depth] reader)
private def subgroup := val (build child [.reference .depth] reader)
private def member := val (build (leaf 0) [] reader)
private def filtered := (run (withoutSelfReference .depth raw) reader).1
private def values := unionMembers raw
private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem raw_call : build body [.reference .depth] reader = .done raw reader := by cbv
private theorem child_call : build child [.reference .depth] reader = .done subgroup reader := by cbv
private def last := val (build (leaf 2) [.reference .depth] reader)
private theorem inputs_available : InternedNestedProvenance.Values reader [.reference .depth] := by
  intro value member
  obtain rfl := List.mem_singleton.mp member
  exact InternedNestedProvenance.depth_available reader
private theorem context : SourceCurrentConstrainedCapSourceHistory.Context reader [.reference .depth] :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ inputs_available,ready.semantic.2⟩
private theorem raw_available : Available reader raw :=
  (InternedFreshOrdinaryFacts.build_verified body _ reader ready.semantic.1.normal.facts inputs_available).result raw reader raw_call
private theorem many_call : buildMany [child,leaf 2] [.reference .depth] reader = .done [subgroup,last] reader := by cbv
private theorem parent_filter : run (withoutSelfReference .depth raw) reader = (filtered,reader) := by cbv
private theorem cold : reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next := by cbv

private theorem checked_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    build body [.reference .depth] reader = .done raw reader ∧
    buildMany [child,leaf 2] [.reference .depth] reader = .done [subgroup,last] reader ∧
    run (withoutSelfReference .depth raw) reader = (filtered,reader) ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next ∧
    ∃ filters outputs middle parentFiltered filterHeap result final,
      FilteredCalls .depth (fun _ => none) [subgroup,last] reader filters outputs middle ∧
      run (withoutSelfReference .depth raw) middle = (parentFiltered,filterHeap) ∧
      execute parentFiltered (fun _ => none) filterHeap = .done result final ∧
      Keeps reader middle ∧ Keeps middle filterHeap ∧ Keeps filterHeap final ∧
      Available final parentFiltered ∧ Available final result ∧
      InternedNestedProvenance.Values final [subgroup,last] ∧
      InternedNestedProvenance.Values final filters ∧ InternedNestedProvenance.Values final outputs ∧
      run (withoutSelfReference .depth raw) final = (parentFiltered,final) ∧
      execute parentFiltered (fun _ => none) final = .done result final ∧
      All₂ (fun member output => run (withoutSelfReference .depth member) final = (output,final)) [subgroup,last] filters ∧
      All₂ (fun member output => execute member (fun _ => none) final = .done output final) filters outputs ∧
      build body [.reference .depth] final = .done raw final ∧
      buildMany [child,leaf 2] [.reference .depth] final = .done [subgroup,last] final ∧
      run (makeUnion [subgroup,last]) final = (raw,final) := by
  refine ⟨actual,ready,raw_call,many_call,parent_filter,cold,?_⟩
  obtain ⟨members,rawHeap,filters,outputs,middle,parentFiltered,filterHeap,result,final,many,_,_,_,
    calls,parentFilter,parentDone,first,second,third,parentAvailable,resultAvailable,membersAvailable,filtersAvailable,outputsAvailable,
    parentWarm,parentStored,filtersWarm,storedWarm,sourceWarm,manyWarm,madeWarm,_⟩ :=
    SourceCurrentGeneratedUnionPreparation.prepare [child,leaf 2] [.reference .depth] reader reader reader context raw raw_call
      ready (grows_refl _) raw_available .depth (fun _ => none) (by intro name value impossible; cases impossible)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (many.symm.trans many_call)
  exact ⟨filters,outputs,middle,parentFiltered,filterHeap,result,final,calls,parentFilter,parentDone,
    first,second,third,parentAvailable,resultAvailable,membersAvailable,filtersAvailable,outputsAvailable,
    parentWarm,parentStored,filtersWarm,storedWarm,sourceWarm,manyWarm,madeWarm⟩

/-- Actual finite preparation makes the cold source subgroup filter and all stored calls warm at its final reader. -/
theorem prepared_cold_subgroup :
    build source [] empty = .done root reader ∧ Ready reader ∧
    build body [.reference .depth] reader = .done raw reader ∧
    buildMany [child,leaf 2] [.reference .depth] reader = .done [subgroup,last] reader ∧
    run (withoutSelfReference .depth raw) reader = (filtered,reader) ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next ∧
    ∃ filters outputs middle parentFiltered filterHeap result final,
      FilteredCalls .depth (fun _ => none) [subgroup,last] reader filters outputs middle ∧
      run (withoutSelfReference .depth raw) middle = (parentFiltered,filterHeap) ∧
      execute parentFiltered (fun _ => none) filterHeap = .done result final ∧
      Keeps reader middle ∧ Keeps middle filterHeap ∧ Keeps filterHeap final ∧
      Available final parentFiltered ∧ Available final result ∧
      InternedNestedProvenance.Values final [subgroup,last] ∧
      InternedNestedProvenance.Values final filters ∧ InternedNestedProvenance.Values final outputs ∧
      run (withoutSelfReference .depth raw) final = (parentFiltered,final) ∧
      execute parentFiltered (fun _ => none) final = .done result final ∧
      All₂ (fun member output => run (withoutSelfReference .depth member) final = (output,final)) [subgroup,last] filters ∧
      All₂ (fun member output => execute member (fun _ => none) final = .done output final) filters outputs ∧
      build body [.reference .depth] final = .done raw final ∧
      buildMany [child,leaf 2] [.reference .depth] final = .done [subgroup,last] final ∧
      run (makeUnion [subgroup,last]) final = (raw,final) := checked_witness
end MicroCFTA.UnionPreparationKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.UnionPreparationKernels.prepared_cold_subgroup
#print MicroCFTA.UnionPreparationKernels.prepared_cold_subgroup
#print axioms MicroCFTA.UnionPreparationKernels.prepared_cold_subgroup
