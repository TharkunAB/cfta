import MicroCFTA.InternedGuardedSmartBudgetDeepSyntax
import MicroCFTA.InternedGuardedBudgetSyntax

/-!
# Raw compiler budgets are included in smart plan budgets

The captured languages satisfy their existing shape root bounds and include
their literal roots. Upward budget inputs supply upward closed candidates.
An unused smart binder removes only root local alternatives from its body.
-/
namespace MicroCFTA.BinderBudgetLanguage

/-- Inclusion on upward candidates is sufficient for budgeted Mu inclusion. -/
theorem mu_mono_upward (left right : Lang Symbol → Lang Symbol)
    (included : ∀ candidate, Upward candidate → Included (left candidate) (right candidate)) :
    Included (mu left) (mu right) := by
  intro budget term accepted candidate upward closed
  apply accepted candidate upward
  rintro bound term ⟨smaller, less, before⟩
  exact closed bound term ⟨smaller, less, included candidate upward smaller term before⟩

end MicroCFTA.BinderBudgetLanguage

namespace MicroCFTA.InternedGuardedBudgetPlanRefinement
open Language InternedNestedConstruction
open InternedDepthSemantics (Shape)
open InternedGuardedSmartBudgetSupport
open BinderBudgetLanguage (Lang Included Upward)

mutual
/-- Raw lexical plans retain every accepted term at the same smart unfolding budget. -/
theorem evaluate_refines {Atom : Type} (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (shapes : List (Shape Atom)) (ambient : Atom → Lang Symbol) (environment : List (Lang Symbol))
    (inputs : DeepInputs shapes ambient ambient environment environment)
    (upward : ∀ index : Nat, Upward (environment[index]?.getD (fun _ _ => False))) :
    Included (InternedGuardedBudgetSyntax.evaluate holds environment expression)
      (InternedGuardedSmartBudget.evaluate holds shapes environment expression) := by
  cases expression with
  | empty => rw [InternedGuardedBudgetSyntax.evaluate, InternedGuardedSmartBudget.evaluate]; exact fun _ _ impossible => impossible
  | var index => rw [InternedGuardedBudgetSyntax.evaluate, InternedGuardedSmartBudget.evaluate]; exact fun _ _ accepted => accepted
  | node edges =>
      rw [InternedGuardedBudgetSyntax.evaluate, InternedGuardedSmartBudget.evaluate]
      rintro budget term ⟨edge, accepted⟩
      exact ⟨edge, edge_refines holds edge.val shapes ambient environment inputs upward budget term accepted⟩
  | union members =>
      rw [InternedGuardedBudgetSyntax.evaluate, InternedGuardedSmartBudget.evaluate]
      rintro budget term ⟨member, accepted⟩
      exact ⟨member, evaluate_refines holds member.val shapes ambient environment inputs upward budget term accepted⟩
  | binder smart body =>
      let innerShapes := (⟨[Sum.inl ()], [], false, 0⟩ : Shape (Sum Unit Atom)) :: shapes.map (Shape.map Sum.inr)
      have liftedUpward (candidate : Lang Symbol) (current : Upward candidate) :
          ∀ index : Nat, Upward ((candidate :: environment)[index]?.getD (fun _ _ => False)) := by
        intro index
        cases index with
        | zero => exact current
        | succ index => exact upward index
      rw [InternedGuardedBudgetSyntax.evaluate, InternedGuardedSmartBudget.evaluate]
      by_cases keep : (!smart || InternedDepthSemantics.hasLocal (InternedDepthSemantics.evaluate body innerShapes).deep) = true
      · simp only [innerShapes] at keep
        simp only [keep, ↓reduceIte]
        apply BinderBudgetLanguage.mu_mono_upward
        intro candidate candidateUpward
        exact evaluate_refines holds body innerShapes (extend ambient candidate) (candidate :: environment)
          (deep_inputs_binder shapes ambient ambient environment environment inputs candidate candidate) (liftedUpward candidate candidateUpward)
      · simp only [innerShapes] at keep
        simp only [keep, Bool.false_eq_true, ↓reduceIte]
        let target := InternedGuardedSmartBudget.evaluate holds innerShapes ((fun _ _ => False) :: environment) body
        have targetUpward : Upward target := InternedGuardedSmartBudget.evaluate_upward holds body innerShapes _
          (liftedUpward (fun _ _ => False) (fun _ _ _ _ impossible => impossible))
        apply BinderBudgetLanguage.least_le _ target targetUpward
        rintro budget term ⟨smaller, less, accepted⟩
        have before := evaluate_refines holds body innerShapes (extend ambient target) (target :: environment)
          (deep_inputs_binder shapes ambient ambient environment environment inputs target target) (liftedUpward target targetUpward)
          smaller term accepted
        have compared := evaluate_deep holds body innerShapes (extend ambient target) (extend ambient (fun _ _ => False))
          (target :: environment) ((fun _ _ => False) :: environment)
          (deep_inputs_binder shapes ambient ambient environment environment inputs target (fun _ _ => False))
        have agree : Agree (extend ambient target) (extend ambient (fun _ _ => False))
            (InternedDepthSemantics.evaluate body innerShapes).deep := by
          intro name member
          cases name with
          | inl token =>
              cases token
              apply False.elim
              apply keep
              have used : InternedDepthSemantics.hasLocal (InternedDepthSemantics.evaluate body innerShapes).deep = true :=
                List.any_eq_true.mpr ⟨.inl (), member, rfl⟩
              simp only [innerShapes] at used
              simp only [used, Bool.or_true]
          | inr name => rfl
        apply targetUpward smaller budget (Nat.le_of_lt less) term
        rcases compared.deep_change agree smaller term before with accepted | ⟨name, member, accepted⟩
        · exact accepted
        · cases name with
          | inl token => exact accepted
          | inr name => exact compared.root_right smaller term ⟨.inr name, member, accepted⟩
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Full raw source edges retain their guards, children, and original smart budget bound. -/
theorem edge_refines {Atom : Type} (holds : Guard → Term Symbol → Bool) (edge : EdgeSyntax Symbol Guard)
    (shapes : List (Shape Atom)) (ambient : Atom → Lang Symbol) (environment : List (Lang Symbol))
    (inputs : DeepInputs shapes ambient ambient environment environment)
    (upward : ∀ index : Nat, Upward (environment[index]?.getD (fun _ _ => False))) :
    Included (InternedGuardedBudgetSyntax.edgeMeaning holds environment edge)
      (InternedGuardedSmartBudget.edgeMeaning holds shapes environment edge) := by
  cases edge with
  | mk symbol guard children =>
      rw [InternedGuardedBudgetSyntax.edgeMeaning, InternedGuardedSmartBudget.edgeMeaning]
      rintro budget term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_refines holds children terms shapes ambient environment inputs upward budget runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Raw ordered forests retain acceptance at their original smart unfolding bound. -/
theorem forest_refines {Atom : Type} (holds : Guard → Term Symbol → Bool)
    (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol)) (shapes : List (Shape Atom))
    (ambient : Atom → Lang Symbol) (environment : List (Lang Symbol))
    (inputs : DeepInputs shapes ambient ambient environment environment)
    (upward : ∀ index : Nat, Upward (environment[index]?.getD (fun _ _ => False))) (budget : Nat)
    (accepted : InternedGuardedBudgetSyntax.forest holds environment budget children terms) :
    InternedGuardedSmartBudget.forest holds shapes environment budget children terms := by
  cases children with
  | nil => cases terms <;> simp only [InternedGuardedBudgetSyntax.forest, InternedGuardedSmartBudget.forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [InternedGuardedBudgetSyntax.forest] at accepted
      | cons term terms =>
          rw [InternedGuardedBudgetSyntax.forest] at accepted
          rw [InternedGuardedSmartBudget.forest]
          exact ⟨evaluate_refines holds child shapes ambient environment inputs upward budget term accepted.1,
            forest_refines holds rest terms shapes ambient environment inputs upward budget accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

end MicroCFTA.InternedGuardedBudgetPlanRefinement
