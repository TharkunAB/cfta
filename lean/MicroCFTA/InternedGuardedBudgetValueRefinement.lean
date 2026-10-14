import MicroCFTA.InternedGuardedBudgetPlanRefinement
import MicroCFTA.InternedGuardedSmartBudgetValues

/-!
# Actual captured records supply raw-to-smart budget refinement

Literal roots come from actual stored references and union members. Stored
nodes and Mu records have no literal root alternative. Upward ambient inputs
therefore give the complete comparison for every actual captured record list.
-/
namespace MicroCFTA.InternedGuardedBudgetPlanRefinement
open Language InternedConstructorTemplates
open InternedNestedConstruction (Syntax)
open InternedGuardedBudget (Env meaning)
open InternedGuardedSmartBudgetSupport
open InternedRecordDepthShape (shape)
open BinderBudgetLanguage (Included Upward)

/-- Every actual stored literal root enters the full budget language at the same bound. -/
theorem shape_lower (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (value : Value Symbol Guard) :
    Lower ambient (shape value) (meaning holds ambient value) := by
  cases value with
  | empty | node | mu =>
      rintro budget term ⟨name, member, _⟩
      simp only [shape, List.not_mem_nil] at member
  | reference name =>
      rintro budget term ⟨selected, member, accepted⟩
      simp only [shape, List.mem_singleton] at member
      subst selected
      rw [meaning]
      exact accepted
  | union entry members depth free =>
      rintro budget term ⟨name, member, accepted⟩
      rw [shape] at member
      change name ∈ (InternedDepthSemantics.combineMany (InternedRecordDepthShape.shapes members)).roots at member
      rw [combined_roots, InternedRecordDepthShape.shapes_map] at member
      obtain ⟨selected, present, named⟩ := member
      obtain ⟨child, childIn, rfl⟩ := List.mem_map.mp present
      rw [meaning]
      have smaller := List.sizeOf_lt_of_mem childIn
      exact ⟨⟨child, childIn⟩, shape_lower holds ambient child budget term ⟨name, named, accepted⟩⟩
termination_by sizeOf value
decreasing_by all_goals simp_wf; all_goals omega

/-- Actual captured record lists satisfy the required root and deep input relations. -/
theorem values_deep_inputs (holds : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard)) (ambient : Env Symbol) :
    DeepInputs (values.map shape) ambient ambient (values.map (meaning holds ambient)) (values.map (meaning holds ambient)) := by
  intro index
  cases found : values[index]? with
  | none =>
      simpa only [List.getElem?_map, found, Option.map_none, Option.getD_none] using
        deep_rootless {} ambient ambient (fun _ _ => False) (fun _ _ => False) (related_empty ambient ambient) rfl
  | some value =>
      simpa only [List.getElem?_map, found, Option.map_some, Option.getD_some] using
        deep_self ambient (shape value) (meaning holds ambient value)
          (InternedGuardedSmartBudgetValues.shape_upper holds ambient value) (shape_lower holds ambient value)

/-- Upward ambient references give upward budget languages at every captured input position. -/
theorem values_upward (holds : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard)) (ambient : Env Symbol)
    (upward : ∀ name, Upward (ambient name)) :
    ∀ index : Nat, Upward ((values.map (meaning holds ambient))[index]?.getD (fun _ _ => False)) := by
  intro index
  cases found : values[index]? with
  | none =>
      simp only [List.getElem?_map, found, Option.map_none, Option.getD_none]
      exact fun _ _ _ _ impossible => impossible
  | some value =>
      simpa only [List.getElem?_map, found, Option.map_some, Option.getD_some] using
        InternedGuardedBudget.meaning_upward holds value ambient upward

/-- Raw plans over actual captures retain every term at its original exact smart budget. -/
theorem values_refine (holds : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard))
    (expression : Syntax Symbol Guard) (ambient : Env Symbol) (upward : ∀ name, Upward (ambient name)) :
    Included (InternedGuardedBudgetSyntax.evaluate holds (values.map (meaning holds ambient)) expression)
      (InternedGuardedSmartBudget.evaluate holds (values.map shape) (values.map (meaning holds ambient)) expression) :=
  evaluate_refines holds expression (values.map shape) ambient (values.map (meaning holds ambient))
    (values_deep_inputs holds values ambient) (values_upward holds values ambient upward)

end MicroCFTA.InternedGuardedBudgetPlanRefinement
