import MicroCFTA.SourceCurrentGeneratedVariableFilter
namespace MicroCFTA.VariableFilterKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentUsedBinderAliasTransport (Scope)
open SourceEqualityRequiredCache (Ready)
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def leaf : Syntax Nat Bool := .node [.mk 3 true []]
private def body : Syntax Nat Bool := .union [.var 0,leaf]
private def source : Syntax Nat Bool := .binder false body
private def built := build source [] empty
private def root := val built
private def reader := built.state
private def raw := val (build body [.reference .depth] reader)
private def result := val (build leaf [] reader)
private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem available : Available reader raw := by
  apply (InternedFreshOrdinaryFacts.build_verified body [.reference .depth] reader ready.semantic.1.normal.facts ?_).result raw reader
  · cbv
  · intro value member
    obtain rfl := List.mem_singleton.mp member
    exact InternedNestedProvenance.depth_available reader
private def firstMap : Environment Nat Bool := fun _ => none
private def secondMap : Environment Nat Bool := fun name => if name = .uninterned 99 then some .empty else none
private theorem agree : ∀ name ∈ raw.free, firstMap name = secondMap name := by
  intro name member
  have free : raw.free = [.depth] := by cbv
  rw [free] at member
  obtain rfl := List.mem_singleton.mp member
  rfl
private def firstNames : Unit → Reference := fun _ => .uninterned 1
private def secondNames : Unit → Reference := fun _ => .uninterned 2
private def refFirst : Environment Nat Bool := fun name => if name = .uninterned 1 then some .empty else none
private def refSecond : Environment Nat Bool := fun name => if name = .uninterned 2 then some .empty else none
private theorem checked_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader raw ∧
    raw ≠ result ∧ run (withoutSelfReference .depth raw) reader = (result,reader) ∧
    (Generated reader result result ∧ Generated reader result result) ∧
    (result.referenceOf = .empty ↔ result.referenceOf = .empty) ∧
    (Generated reader (.empty : Value Nat Bool) .empty ∧ Generated reader .empty .empty) ∧
    (((.empty : Value Nat Bool).referenceOf = .empty) ↔ (.empty : Value Nat Bool).referenceOf = .empty) := by
  have fixedInputs : Inputs reader firstMap secondMap [raw] [raw] := .fixed raw agree (.nil _ _)
  have fixed := SourceCurrentGeneratedVariableFilter.variable_call reader ready
    ([.inl raw] : List (Sum (Value Nat Bool) Unit)) (fun _ => .depth) (fun _ => .depth)
    .depth .depth firstMap secondMap fixedInputs 0 raw raw result result result result available
    (by intro label member; exact Iff.rfl) (by simp only [build,List.map_cons,List.map_nil,List.getElem?_cons_zero,input,Option.getD_some])
    (by simp only [build,List.map_cons,List.map_nil,List.getElem?_cons_zero,input,Option.getD_some])
    (by cbv) (by cbv) (by cbv) (by cbv)
    (by intro a b impossible; cbv at impossible; cases impossible)
  have refs : Inputs reader refFirst refSecond [.reference (.uninterned 1)] [.reference (.uninterned 2)] :=
    .reference (by change Generated reader .empty .empty; exact .refl _) (by change Generated reader .empty .empty; exact .refl _) (.nil _ _)
  have reference := SourceCurrentGeneratedVariableFilter.variable_call reader ready
    ([.inr ()] : List (Sum (Value Nat Bool) Unit)) firstNames secondNames
    (.uninterned 1) (.uninterned 2) refFirst refSecond refs 0
    (.reference (.uninterned 1)) (.reference (.uninterned 2))
    (.reference (.uninterned 1)) (.reference (.uninterned 2)) .empty .empty
    (reference_available _ _ (InternedFreshProbeKeys.sentinel_references_issued _ 1).2)
    (by
      intro label member
      simp only [Scope,SourceCurrentNativeNormalizationInputs.support,InternedFreeNameSemantics.evaluate,
        List.map_cons,List.map_nil,List.getElem?_cons_zero,Option.getD_some,SourceCurrentNativeNormalizationInputs.inputNames,
        List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> simp [firstNames,secondNames])
    (by simp only [build,List.map_cons,List.map_nil,List.getElem?_cons_zero,input,Option.getD_some,firstNames])
    (by simp only [build,List.map_cons,List.map_nil,List.getElem?_cons_zero,input,Option.getD_some,secondNames])
    rfl rfl (by cbv) (by cbv)
    (by intro a b same other; cases same; cases other; exact Iff.rfl)
  refine ⟨actual,ready,available,?_,by cbv,fixed.1,fixed.2,reference.1,reference.2⟩
  cbv
  intro impossible
  cases impossible

/-- Source-built fixed union filtering and varying reference resolution invoke the filtered variable producer. -/
theorem fixed_and_reference :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader raw ∧
    raw ≠ result ∧ run (withoutSelfReference .depth raw) reader = (result,reader) ∧
    (Generated reader result result ∧ Generated reader result result) ∧
    (result.referenceOf = .empty ↔ result.referenceOf = .empty) ∧
    (Generated reader (.empty : Value Nat Bool) .empty ∧ Generated reader .empty .empty) ∧
    (((.empty : Value Nat Bool).referenceOf = .empty) ↔ (.empty : Value Nat Bool).referenceOf = .empty) := checked_witness
end MicroCFTA.VariableFilterKernels
