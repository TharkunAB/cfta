import MicroCFTA.SourceCurrentFixedReaderUnionFragments

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.FixedReaderUnionFragmentsKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentStoredNodeExpansion (RowCalls)

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol true []]
private def child : Syntax Nat Bool := .union [.var 0,leaf 0,leaf 1]
private def expressions : List (Syntax Nat Bool) := [child,leaf 2]
private def body : Syntax Nat Bool := .union expressions
private def source : Syntax Nat Bool := .binder false body
private def built := build source [] empty
private def root := val built
private def reader := built.state
private def raw := val (build body [.reference .depth] reader)
private def subgroup := val (build child [.reference .depth] reader)
private def filtered := (run (withoutSelfReference .depth raw) reader).1
private def nullMap : InternedStoredSubstitution.Environment Nat Bool := fun _ => none
private def emptyDepth : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .depth then some .empty else none
private def firstRow : EdgeValue Nat Bool := (run (makeEdge 0 true []) reader).1

private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem raw_call : build body [.reference .depth] reader = .done raw reader := by cbv
private theorem context : Context reader [.reference .depth] :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ (by
      intro value member
      obtain rfl := List.mem_singleton.mp member
      exact InternedNestedProvenance.depth_available reader), ready.semantic.2⟩
private theorem raw_available : Available reader raw :=
  (InternedFreshOrdinaryFacts.build_verified body _ reader context.base.normal.facts context.base.inputs).result
    raw reader raw_call

private theorem raw_literals (atom : Value Nat Bool) (part : Literal raw atom) : atom = .reference .depth := by
  cbv at part
  cases part with
  | union member found =>
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> cases found
      rfl

private theorem checked_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    build body [.reference .depth] reader = .done raw reader ∧
    run (withoutSelfReference .depth raw) reader = (filtered,reader) ∧
    execute filtered nullMap reader = .done filtered reader ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next ∧
    reader.nodes.next < (execute subgroup emptyDepth reader).state.nodes.next ∧
    ∃ values middle output,
      buildMany expressions [.reference .depth] reader = .done values middle ∧
      values[0]? = some subgroup ∧
      All₂ (fun expression value => ∃ current returned,
        Context current [.reference .depth] ∧ build expression [.reference .depth] current = .done value returned ∧
        Grows returned reader ∧ build expression [.reference .depth] reader = .done value reader) expressions values ∧
      RowCalls nullMap reader firstRow output ∧ Row filtered output ∧
      ∃ (index : Nat) (member : Value Nat Bool) (original : EdgeValue Nat Bool),
        values[index]? = some member ∧ Row member original ∧ RowCalls nullMap reader original output ∧
        (!(output.children.any (fun child => child.referenceOf == .empty))) = true := by
  have filterCall : run (withoutSelfReference .depth raw) reader = (filtered,reader) := by cbv
  have storedCall : execute filtered nullMap reader = .done filtered reader := by cbv
  obtain ⟨values,middle,many,_middleContext,_made,_growth,_available,_manyWarm,_madeWarm,sources,
    _literals,rows,_atoms,rowCalls⟩ := SourceCurrentFixedReaderUnionFragments.source expressions [.reference .depth]
      reader reader reader context raw raw_call ready (grows_refl reader) raw_available .depth nullMap
      (by intro name value impossible; cases impossible) filtered filtered filterCall storedCall
  have observed : buildMany expressions [.reference .depth] reader =
      .done [subgroup,val (build (leaf 2) [.reference .depth] reader)] reader := by cbv
  have exactValues := (Outcome.done.inj (many.symm.trans observed)).1
  have selected : values[0]? = some subgroup := by rw [exactValues]; rfl
  have original : Row subgroup firstRow := by cbv; exact .union (List.mem_cons_of_mem _ List.mem_cons_self) (.node List.mem_cons_self)
  obtain ⟨output,called⟩ := rowCalls 0 subgroup firstRow selected original
  have actualRow : RowCalls nullMap reader firstRow firstRow := by
    have children : firstRow.children = [] := by cbv
    unfold RowCalls
    rw [children]
    exact ⟨.nil reader,by cbv,rfl,rfl,rfl⟩
  have emptyChildren : output.children = [] := List.length_eq_zero.mp (by
    simpa only [firstRow,List.length_nil] using called.2.2.2.2)
  have same : output = firstRow := by
    have first := called.2.1
    rw [emptyChildren] at first
    exact congrArg Prod.fst (first.symm.trans actualRow.2.1)
  have found : Row filtered output := by rw [same]; cbv; exact .node (Or.inl rfl)
  have covered := (rows output).mp found
  have ordinary : ∃ (index : Nat) (member : Value Nat Bool) (original : EdgeValue Nat Bool),
      values[index]? = some member ∧ Row member original ∧ RowCalls nullMap reader original output ∧
      (!(output.children.any (fun child => child.referenceOf == .empty))) = true := by
    rcases covered with atom | ordinary
    · obtain ⟨index,member,source,_rebuilt,present,part,retained,_executed,_inside⟩ := atom
      have parentLiteral := (SourceCurrentLiteralUnionParts.literal reader ready.semantic.1.normal.facts
        values _available source).mpr ⟨member,List.mem_of_getElem? present,part⟩
      rw [_madeWarm] at parentLiteral
      have localOnly := raw_literals source parentLiteral
      rcases retained with bare | different
      · cbv at bare
        cases bare
      · exact False.elim (different localOnly)
    · exact ordinary
  exact ⟨actual,ready,raw_call,filterCall,storedCall,by cbv,by cbv,
    values,middle,output,many,selected,sources,called,found,ordinary⟩

/-- The warm parent exposes original row calls while its proper ordinary subgroup still allocates. -/
theorem warm_parent_cold_subgroup :
    build source [] empty = .done root reader ∧ Ready reader ∧
    build body [.reference .depth] reader = .done raw reader ∧
    run (withoutSelfReference .depth raw) reader = (filtered,reader) ∧
    execute filtered nullMap reader = .done filtered reader ∧
    reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next ∧
    reader.nodes.next < (execute subgroup emptyDepth reader).state.nodes.next ∧
    ∃ values middle output,
      buildMany expressions [.reference .depth] reader = .done values middle ∧
      values[0]? = some subgroup ∧
      All₂ (fun expression value => ∃ current returned,
        Context current [.reference .depth] ∧ build expression [.reference .depth] current = .done value returned ∧
        Grows returned reader ∧ build expression [.reference .depth] reader = .done value reader) expressions values ∧
      RowCalls nullMap reader firstRow output ∧ Row filtered output ∧
      ∃ (index : Nat) (member : Value Nat Bool) (original : EdgeValue Nat Bool),
        values[index]? = some member ∧ Row member original ∧ RowCalls nullMap reader original output ∧
        (!(output.children.any (fun child => child.referenceOf == .empty))) = true := checked_witness

end MicroCFTA.FixedReaderUnionFragmentsKernels
