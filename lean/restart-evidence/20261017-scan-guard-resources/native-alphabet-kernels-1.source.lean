import MicroCFTA.SourceCurrentNativeGuardAlphabet

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.NativeAlphabetKernels
open SourceCurrentNativeGuardAlphabet
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

private def first : Guard := ⟨some [[[0], [1]]], .same [0] [1]⟩
private def second : Guard := ⟨some [], .entails [1] [2]⟩

/-- The literal source conjunction keeps both operand orders in the finite list. -/
theorem ordered_source_step :
    step [first, second] = [first, second, top,
      conjoin first first, conjoin first second, conjoin second first, conjoin second second] ∧
    (step [first, second]).length = 7 ∧
    conjoin first second ∈ step [first, second] ∧ conjoin second first ∈ step [first, second] := by
  refine ⟨rfl, ?_, conjoin_mem_step (by simp) (by simp), conjoin_mem_step (by simp) (by simp)⟩
  rw [step_length]
  rfl

/-- Two actual source conjunction levels are covered without an execution premise. -/
theorem nested_source_schedule :
    step [] = [top] ∧
    conjoin (conjoin first second) second ∈ advance [first, second] 2 ∧
    advance [first, second] (1 + 2) = advance (advance [first, second] 1) 2 ∧
    (advance [first, second] 2).length = 57 ∧
    advance [first, second] 2 ⊆ advance [first, second] 3 := by
  have firstIn : first ∈ [first, second] := by simp
  have secondIn : second ∈ [first, second] := by simp
  have pairIn : conjoin first second ∈ advance [first, second] 1 :=
    conjoin_mem_advance 0 firstIn secondIn
  have retained : second ∈ advance [first, second] 1 := mem_advance_of_mem secondIn 1
  refine ⟨rfl, conjoin_mem_advance 1 pairIn retained, advance_add _ 1 2, ?_,
    advance_count_mono _ (by omega)⟩
  rw [advance_step, step_length, advance_step, step_length, advance_zero]
  rfl

#print axioms ordered_source_step
#check @ordered_source_step
#print ordered_source_step
#print axioms nested_source_schedule
#check @nested_source_schedule
#print nested_source_schedule
end MicroCFTA.NativeAlphabetKernels
