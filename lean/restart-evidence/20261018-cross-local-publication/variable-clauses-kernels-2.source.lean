import MicroCFTA.SourceCurrentGeneratedVariableClauses

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.GeneratedVariableClausesKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentLiteralLocalSimulation (Clauses)
open SourceCurrentUsedBinderAliasTransport (Scope)
open InternedFreshOrdinaryDepthHeap (usesLocal)

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol true []]
private def merged : Syntax Nat Bool := .node [.mk 0 true [],.mk 1 true []]
private def recursive : Syntax Nat Bool := .binder false (.node [.mk 7 false [.var 0]])
private def source : Syntax Nat Bool := .node [.mk 99 false [leaf 0,leaf 1,merged,recursive]]
private def built := build source [] empty
private def root := val built
private def reader := built.state
private def left := val (build (leaf 0) [] reader)
private def right := val (build merged [] reader)
private def leaf1 := val (build (leaf 1) [] reader)
private def mu := val (build recursive [] reader)
private def inputs : List (Sum (Value Nat Bool) Unit) := [.inr (),.inl mu]
private def firstNames : Unit → Reference := fun _ => .uninterned 10
private def secondNames : Unit → Reference := fun _ => .uninterned 20
private def own : Reference := .uninterned 100
private def firstMap : Environment Nat Bool := fun name => if name = .uninterned 10 then some left else none
private def secondMap : Environment Nat Bool := fun name => if name = .uninterned 20 then some right else none
private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem available (term : Syntax Nat Bool) (value : Value Nat Bool)
    (actual : build term [] reader = .done value reader) : Available reader value :=
  (InternedFreshOrdinaryFacts.build_verified term [] reader ready.semantic.1.normal.facts
    (by intro value impossible; cases impossible)).result value reader actual
private theorem mu_available : Available reader mu := available recursive mu (by cbv)
private theorem reflexive (value : Value Nat Bool) : Clauses reader Eq value value :=
  SourceCurrentLiteralLocalSimulation.below reader Eq (fun _ => rfl) value value
    (SourceCurrentSourceDirectedCases.Below.refl value)
private theorem included : SourceCurrentSourceDirectedCases.Below left right := by
  have values : InternedNestedProvenance.Values reader [left,leaf1] := by
    intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact available (leaf 0) left (by cbv)
    · exact available (leaf 1) leaf1 (by cbv)
  have made : run (makeUnion [left,leaf1]) reader = (right,reader) := by cbv
  have result := SourceCurrentSourceDirectedCases.union_member [left,leaf1] reader ready.semantic.1.normal values left List.mem_cons_self
  rw [made] at result
  exact result
private theorem lexical_clause : Clauses reader Eq left right :=
  SourceCurrentLiteralLocalSimulation.below reader Eq (fun _ => rfl) left right included
private theorem same_slot (value : Value Nat Bool) (agree : ∀ name ∈ value.free, firstMap name = secondMap name) :
    Slot (Clauses reader Eq) firstMap secondMap value value := by
  cases value with
  | reference name =>
      change Clauses reader Eq ((firstMap name).getD _) ((secondMap name).getD _)
      rw [agree name (by simp only [Value.free,List.mem_singleton])]
      exact reflexive _
  | empty | node | union | mu => exact ⟨rfl,agree⟩
private theorem paired : Paired (Clauses reader Eq) firstMap secondMap
    (inputs.map (input firstNames)) (inputs.map (input secondNames)) := by
  refine .cons ?_ (.cons (same_slot mu ?_) .nil)
  · change Clauses reader Eq ((firstMap (.uninterned 10)).getD _) ((secondMap (.uninterned 20)).getD _)
    simpa only [firstMap,secondMap,ite_true,Option.getD_some] using lexical_clause
  · intro name member
    have closed : mu.free = [] := by cbv
    rw [closed] at member
    cases member
private theorem tests0 : ∀ label ∈ Scope (.var 0) inputs,
    Sum.elim id firstNames label = own ↔ Sum.elim id secondNames label = own := by
  intro label member
  have scope : Scope (.var 0) inputs = [.inl .depth,.inr ()] := by cbv
  rw [scope] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> exact iff_of_false (by decide) (by decide)
private theorem tests1 : ∀ label ∈ Scope (.var 1) inputs,
    Sum.elim id firstNames label = own ↔ Sum.elim id secondNames label = own := by
  intro label member
  have scope : Scope (.var 1) inputs = [.inl .depth] := by cbv
  rw [scope] at member
  obtain rfl := List.mem_singleton.mp member
  exact Iff.rfl
private theorem tests9 : ∀ label ∈ Scope (.var 9) inputs,
    Sum.elim id firstNames label = own ↔ Sum.elim id secondNames label = own := by
  intro label member
  have scope : Scope (.var 9) inputs = [.inl .depth] := by cbv
  rw [scope] at member
  obtain rfl := List.mem_singleton.mp member
  exact Iff.rfl

private theorem checked :
    build source [] empty = .done root reader ∧ Ready reader ∧ left ≠ right ∧
    (match mu with | .mu _ _ depth ordinary => usesLocal depth ordinary | _ => false) = true ∧
    execute (.reference (.uninterned 10)) firstMap reader = .done left reader ∧
    execute (.reference (.uninterned 20)) secondMap reader = .done right reader ∧
    execute mu firstMap reader = .done mu reader ∧ execute mu secondMap reader = .done mu reader ∧
    Clauses reader Eq left right ∧ Clauses reader Eq mu mu ∧ Clauses reader Eq .empty .empty := by
  have referenceCase := SourceCurrentGeneratedVariableClauses.variable_call Eq (fun _ => rfl) reader ready
    inputs firstNames secondNames own own firstMap secondMap paired 0
    (.reference (.uninterned 10)) (.reference (.uninterned 20))
    (.reference (.uninterned 10)) (.reference (.uninterned 20)) left right
    (InternedNestedProvenance.ordinary_available reader 10) tests0
    (firstBefore := reader) (firstAfter := reader) (secondBefore := reader) (secondAfter := reader)
    (by cbv) (by cbv) rfl rfl (by cbv) (by cbv)
  have fixedCase := SourceCurrentGeneratedVariableClauses.variable_call Eq (fun _ => rfl) reader ready
    inputs firstNames secondNames own own firstMap secondMap paired 1 mu mu mu mu mu mu mu_available tests1
    (firstBefore := reader) (firstAfter := reader) (secondBefore := reader) (secondAfter := reader)
    (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
  have missingCase := SourceCurrentGeneratedVariableClauses.variable_call Eq (fun _ => rfl) reader ready
    inputs firstNames secondNames own own firstMap secondMap paired 9 .empty .empty .empty .empty .empty .empty
    (empty_available reader) tests9
    (firstBefore := reader) (firstAfter := reader) (secondBefore := reader) (secondAfter := reader)
    (by cbv) (by cbv) rfl rfl (by cbv) (by cbv)
  have different : left ≠ right := by cbv; intro same; cases same
  have used : (match mu with | .mu _ _ depth ordinary => usesLocal depth ordinary | _ => false) = true := by cbv
  exact ⟨actual,ready,different,used,by cbv,by cbv,by cbv,by cbv,referenceCase,fixedCase,missingCase⟩

/-- Actual variables cover distinct resolved ordinary values, a fixed used Mu, and a missing index. -/
theorem actual_variable_cases :
    build source [] empty = .done root reader ∧ Ready reader ∧ left ≠ right ∧
    (match mu with | .mu _ _ depth ordinary => usesLocal depth ordinary | _ => false) = true ∧
    execute (.reference (.uninterned 10)) firstMap reader = .done left reader ∧
    execute (.reference (.uninterned 20)) secondMap reader = .done right reader ∧
    execute mu firstMap reader = .done mu reader ∧ execute mu secondMap reader = .done mu reader ∧
    Clauses reader Eq left right ∧ Clauses reader Eq mu mu ∧ Clauses reader Eq .empty .empty := checked

end MicroCFTA.GeneratedVariableClausesKernels
