import MicroCFTA.SourceCurrentGeneratedHistoricalContext
namespace MicroCFTA.HistoricalContextKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentGeneratedUnionPreparation (FilteredCalls)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
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
private def unused : Value Nat Bool := .reference (.interned 0)
private def inputs : List (Value Nat Bool) := [.reference .depth,unused]
private def raw := val (build body inputs reader)
private def subgroup := val (build child inputs reader)
private def last := val (build (leaf 2) inputs reader)
private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem unused_available : Available reader unused := by
  apply reference_available reader (.interned 0)
  intro identity member
  have same : identity = 0 := by simpa only [Value.free,List.mem_singleton,Reference.interned.injEq] using member
  subst identity
  exact ⟨(reader.nodes.issued 0).getD (.node []),by cbv⟩
private theorem inputs_available : InternedNestedProvenance.Values reader inputs := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact InternedNestedProvenance.depth_available reader
  · obtain rfl := List.mem_singleton.mp member
    exact unused_available
private theorem context : Context reader inputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ inputs_available,ready.semantic.2⟩
private theorem raw_call : build body inputs reader = .done raw reader := by cbv
private theorem many_call : buildMany [child,leaf 2] inputs reader = .done [subgroup,last] reader := by cbv
private theorem cold : reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next := by cbv
private theorem first_pair {Item Other : Type} {relation : Item → Other → Prop}
    {item : Item} {items : List Item} {others : List Other} (paired : All₂ relation (item::items) others) :
    ∃ other rest, others = other::rest ∧ relation item other := by
  cases paired with
  | cons head _ => exact ⟨_,_,rfl,head⟩

private theorem checked_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    Available reader unused ∧ build body inputs reader = .done raw reader ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next ∧
    ∃ filters outputs middle filtered filterHeap result final,
      FilteredCalls .depth (fun _ => none) [subgroup,last] reader filters outputs middle ∧
      run (withoutSelfReference .depth raw) middle = (filtered,filterHeap) ∧
      execute filtered (fun _ => none) filterHeap = .done result final ∧
      Keeps reader final ∧ Context final inputs ∧
      All₂ (fun expression value => build expression inputs final = .done value final)
        [child,leaf 2] [subgroup,last] ∧
      ∃ childFiltered childOutput,
        run (withoutSelfReference .depth subgroup) final = (childFiltered,final) ∧
        execute childFiltered (fun _ => none) final = .done childOutput final ∧
        Generated final childOutput childOutput := by
  refine ⟨actual,ready,unused_available,raw_call,cold,?_⟩
  obtain ⟨values,rawHeap,filters,outputs,middle,filtered,filterHeap,result,final,many,_,_,_,
    calls,parentFilter,parentDone,first,second,third,_,_,_,finalFilters,_,finalContext,whole,
    _,_,filtersWarm,storedWarm,_,_,_,members⟩ :=
    SourceCurrentGeneratedHistoricalContext.union_prepare [child,leaf 2] inputs reader reader reader context raw raw_call
      (SourceEqualityRequiredCache.pure_keeps reader ready) .depth (fun _ => none)
      (by intro name value impossible; cases impossible)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (many.symm.trans many_call)
  refine ⟨filters,outputs,middle,filtered,filterHeap,result,final,calls,parentFilter,parentDone,
    first.trans (second.trans third),finalContext,members,?_⟩
  obtain ⟨childFiltered,otherFilters,rfl,filterCall⟩ := first_pair filtersWarm
  obtain ⟨childOutput,otherOutputs,rfl,storedCall⟩ := first_pair storedWarm
  obtain ⟨_,_,_,childCall⟩ := first_pair members
  have childCall : build child inputs final = .done subgroup final := childCall
  have filteredAvailable : Available final childFiltered := finalFilters _ List.mem_cons_self
  let symbolic : List (Sum (Value Nat Bool) Unit) := [.inl (.reference .depth),.inl unused]
  let names : Unit → Reference := fun _ => .depth
  have interpreted : symbolic.map (input names) = inputs := rfl
  have paired : Inputs final (fun _ => none) (fun _ => none) inputs inputs :=
    .fixed (.reference .depth) (fun _ _ => rfl) (.fixed unused (fun _ _ => rfl) (.nil _ _))
  have generated : Generated final childOutput childOutput := by
    apply Generated.filtered child symbolic names names .depth .depth (fun _ => none) (fun _ => none)
      final final final final final final subgroup subgroup childFiltered childFiltered childOutput childOutput
      whole.ready
      (by simpa only [interpreted] using finalContext) (by simpa only [interpreted] using finalContext)
      (by intro a am b bm; rfl) (by intro label member; rfl)
      (by simpa only [interpreted] using paired)
      (by intro name value impossible; cases impossible) (by intro name value impossible; cases impossible)
      filteredAvailable filteredAvailable
      (by simpa only [interpreted] using childCall) (by simpa only [interpreted] using childCall)
      filterCall filterCall (grows_refl _) (grows_refl _) (grows_refl _) (grows_refl _)
      (by simpa only [interpreted] using childCall) (by simpa only [interpreted] using childCall)
      filterCall filterCall storedCall storedCall
  exact ⟨childFiltered,childOutput,filterCall,storedCall,generated⟩

theorem cold_subgroup_adjacent :
    build source [] empty = .done root reader ∧ Ready reader ∧
    Available reader unused ∧ build body inputs reader = .done raw reader ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next ∧
    ∃ filters outputs middle filtered filterHeap result final,
      FilteredCalls .depth (fun _ => none) [subgroup,last] reader filters outputs middle ∧
      run (withoutSelfReference .depth raw) middle = (filtered,filterHeap) ∧
      execute filtered (fun _ => none) filterHeap = .done result final ∧
      Keeps reader final ∧ Context final inputs ∧
      All₂ (fun expression value => build expression inputs final = .done value final)
        [child,leaf 2] [subgroup,last] ∧
      ∃ childFiltered childOutput,
        run (withoutSelfReference .depth subgroup) final = (childFiltered,final) ∧
        execute childFiltered (fun _ => none) final = .done childOutput final ∧
        Generated final childOutput childOutput := checked_witness

end MicroCFTA.HistoricalContextKernels
