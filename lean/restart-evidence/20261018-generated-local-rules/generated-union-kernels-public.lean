import MicroCFTA.SourceCurrentGeneratedUnionCases
namespace MicroCFTA.GeneratedUnionKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentSourceDirectedCases (Below)
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
private theorem values_available : InternedNestedProvenance.Values reader values := by
  have inputs : InternedNestedProvenance.Values reader [.reference .depth] := by
    intro value included
    obtain rfl := List.mem_singleton.mp included
    exact InternedNestedProvenance.depth_available reader
  have available := (InternedFreshOrdinaryFacts.build_verified body _ reader ready.semantic.1.normal.facts inputs).result raw reader raw_call
  intro value included
  exact unionMembers_available raw available value included
private theorem checked_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    build child [.reference .depth] reader = .done subgroup reader ∧
    run (makeUnion values) reader = (raw,reader) ∧
    run (withoutSelfReference .depth raw) reader = (filtered,reader) ∧
    execute member (fun _ => none) reader = .done member reader ∧
    execute filtered (fun _ => none) reader = .done filtered reader ∧
    Below member filtered ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next := by
  have made : run (makeUnion values) reader = (raw,reader) := by cbv
  have firstFilter : run (withoutSelfReference .depth member) reader = (member,reader) := by cbv
  have parentFilter : run (withoutSelfReference .depth raw) reader = (filtered,reader) := by cbv
  have firstDone : execute member (fun _ => none) reader = .done member reader := by cbv
  have secondDone : execute filtered (fun _ => none) reader = .done filtered reader := by cbv
  have fragment := SourceCurrentGeneratedUnionCases.retained_member reader ready values values_available
    member raw member filtered member filtered .depth (fun _ => none)
    (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self) made
    (Or.inl (by cbv; intro impossible; cases impossible)) firstFilter parentFilter
    (by intro name value impossible; cases impossible) firstDone secondDone
  exact ⟨actual,ready,child_call,made,parentFilter,firstDone,secondDone,fragment,by cbv⟩

/-- An actual warm parent filter retains a reconstructed member while its proper subgroup filter still allocates. -/
theorem warm_parent_cold_subgroup :
    build source [] empty = .done root reader ∧ Ready reader ∧
    build child [.reference .depth] reader = .done subgroup reader ∧
    run (makeUnion values) reader = (raw,reader) ∧
    run (withoutSelfReference .depth raw) reader = (filtered,reader) ∧
    execute member (fun _ => none) reader = .done member reader ∧
    execute filtered (fun _ => none) reader = .done filtered reader ∧
    Below member filtered ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next := checked_witness
end MicroCFTA.GeneratedUnionKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

#check @MicroCFTA.GeneratedUnionKernels.warm_parent_cold_subgroup
#print MicroCFTA.GeneratedUnionKernels.warm_parent_cold_subgroup
#print axioms MicroCFTA.GeneratedUnionKernels.warm_parent_cold_subgroup
