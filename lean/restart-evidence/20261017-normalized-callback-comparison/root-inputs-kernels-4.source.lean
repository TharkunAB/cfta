import MicroCFTA.SourceCurrentNativeNormalizationFreshness
import MicroCFTA.SourceCurrentNativeStrippedAlternatives
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 200000000

namespace MicroCFTA.NormalizedInputKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open SourceCurrentNativeNormalizationInputs
open SourceCurrentNativeNormalizationFreshness
open SourceCurrentNativeStrippedAlternatives
open InternedBinderProtocol (Reference)

private def inputs : List (Sum (Value Nat Unit) Bool) :=
  [.inr false, .inr true, .inl (.reference (.uninterned 8))]
private def names (_ : Bool) : Reference := .uninterned 7
private def body : Syntax Nat Unit :=
  .union [.var 1, .var 2, .node [.mk 0 () []], .node [.mk 1 () [.var 3, .empty]]]
private def called := callback body (inputs.map (input names)) .depth empty
private def returned : Value Nat Unit := match called with
  | .done value _ => value
  | .pending _ _ => .empty
private def after : State Nat Unit := called.state

private theorem done : called = .done returned after := by cbv
private theorem context : Context (empty : State Nat Unit) (inputs.map (input names)) := by
  apply SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
  intro value member
  simp only [inputs, List.map_cons, List.map_nil, input] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact InternedNestedProvenance.ordinary_available _ _
  · rcases List.mem_cons.mp member with rfl | member
    · exact InternedNestedProvenance.ordinary_available _ _
    · rcases List.mem_cons.mp member with rfl | impossible
      · exact InternedNestedProvenance.ordinary_available _ _
      · cases impossible

/-- Aliased live varying names coexist with a discarded capture equal to the selected ordinary argument. -/
theorem aliased_probe :
    names false = names true ∧ ordinaryLevel returned = 8 ∧
    .inr false ∈ support (.binder true body) inputs ∧ .inr true ∈ support (.binder true body) inputs ∧
    .uninterned (ordinaryLevel returned) ∉ (support (.binder true body) inputs).map (Sum.elim id names) ∧
    .uninterned 8 ∈ ((inputs.map (input names)).getD 2 .empty).free := by
  refine ⟨rfl, by cbv,
    by change Sum.inr false ∈ [Sum.inr false, Sum.inr true]; exact List.mem_cons_self,
    by change Sum.inr true ∈ [Sum.inr false, Sum.inr true]; exact List.mem_cons_of_mem _ List.mem_cons_self,
    ?_, by change Reference.uninterned 8 ∈ [Reference.uninterned 8]; exact List.mem_cons_self⟩
  exact ordinary body inputs names empty after context returned done

/-- Duplicate removed references retain exact canonical root alternatives on cold and warm union calls. -/
theorem stripped_cold_warm :
    let original := run (makeUnion [Value.reference (Symbol := Nat) (Guard := Unit) (.uninterned 7),
      .reference (.uninterned 7), .reference (.intersection 2 3), .reference (.uninterned 9)]) empty
    stripMany [.uninterned 7, .intersection 2 3, .uninterned 7] (unionMembers original.1) =
      [.reference (.uninterned 9)] ∧
    run (makeUnion [original.1]) original.2 = original := by
  refine ⟨by cbv, ?_⟩
  cbv

#check @aliased_probe
#print axioms aliased_probe
#check @stripped_cold_warm
#print axioms stripped_cold_warm
end MicroCFTA.NormalizedInputKernels
