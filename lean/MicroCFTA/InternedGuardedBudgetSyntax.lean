import MicroCFTA.InternedGuardedBudget

/-!
# Raw unfolding budgets of complete lexical source plans

Variables read budget languages by lexical position. Both binder forms
consume one raw step before their body. This interpretation describes the
plan before smart cleanup. It does not assert exact runtime binder costs.
-/
namespace MicroCFTA.InternedGuardedBudgetSyntax
open InternedNestedConstruction Language
open BinderBudgetLanguage (Lang Included Upward)

mutual
/-- Interpret every lexical branch with one raw unfolding step per binder. -/
def evaluate (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol)) : Syntax Symbol Guard → Lang Symbol
  | .empty => fun _ _ => False
  | .var index => environment[index]?.getD (fun _ _ => False)
  | .node edges => fun budget term => ∃ edge : {edge // edge ∈ edges}, edgeMeaning holds environment edge.val budget term
  | .union members => fun budget term => ∃ member : {member // member ∈ members}, evaluate holds environment member.val budget term
  | .binder _ body => BinderBudgetLanguage.mu (fun language => evaluate holds (language :: environment) body)
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Full lexical edges retain guards and the common child unfolding bound. -/
def edgeMeaning (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol)) : EdgeSyntax Symbol Guard → Lang Symbol
  | .mk symbol guard children => fun budget term => ∃ terms, term = .node symbol terms ∧
      forest holds environment budget children terms ∧ holds guard term = true
termination_by edge => sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordered lexical children retain their common unfolding bound. -/
def forest (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol)) (budget : Nat) :
    List (Syntax Symbol Guard) → List (Term Symbol) → Prop
  | [], [] => True
  | child :: rest, term :: terms => evaluate holds environment child budget term ∧ forest holds environment budget rest terms
  | _, _ => False
termination_by children _ => sizeOf children
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- Every lexical budget interpretation is positive in its input budget languages. -/
theorem evaluate_mono (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ _ => False)) (after[index]?.getD (fun _ _ => False))) :
    Included (evaluate holds before expression) (evaluate holds after expression) := by
  cases expression with
  | empty => rw [evaluate, evaluate]; exact fun _ _ impossible => impossible
  | var index => simpa only [evaluate] using included index
  | node edges =>
      rw [evaluate, evaluate]
      rintro budget term ⟨edge, accepted⟩
      exact ⟨edge, edgeMeaning_mono holds edge.val before after included budget term accepted⟩
  | union members =>
      rw [evaluate, evaluate]
      rintro budget term ⟨member, accepted⟩
      exact ⟨member, evaluate_mono holds member.val before after included budget term accepted⟩
  | binder smart body =>
      rw [evaluate, evaluate]
      apply BinderBudgetLanguage.mu_mono
      intro language
      apply evaluate_mono holds body
      intro index
      cases index with
      | zero => exact fun _ _ accepted => accepted
      | succ index => exact included index
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Full lexical edges retain input-language inclusion at each identical bound. -/
theorem edgeMeaning_mono (holds : Guard → Term Symbol → Bool) (edge : EdgeSyntax Symbol Guard)
    (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ _ => False)) (after[index]?.getD (fun _ _ => False))) :
    Included (edgeMeaning holds before edge) (edgeMeaning holds after edge) := by
  cases edge with
  | mk symbol guard children =>
      rw [edgeMeaning, edgeMeaning]
      rintro budget term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_mono holds children terms before after included budget runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordered lexical forests retain input-language inclusion at their common bound. -/
theorem forest_mono (holds : Guard → Term Symbol → Bool) (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol))
    (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ _ => False)) (after[index]?.getD (fun _ _ => False)))
    (budget : Nat) (accepted : forest holds before budget children terms) : forest holds after budget children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [forest] at accepted
      | cons term terms =>
          rw [forest] at accepted ⊢
          exact ⟨evaluate_mono holds child before after included budget term accepted.1,
            forest_mono holds rest terms before after included budget accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

/-- A raw lexical binder accepts exactly a smaller-bound body derivation. -/
theorem binder_unfold (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol))
    (smart : Bool) (body : Syntax Symbol Guard) (budget : Nat) (term : Term Symbol) :
    evaluate holds environment (.binder smart body) budget term ↔
      ∃ smaller, smaller < budget ∧
        evaluate holds (evaluate holds environment (.binder smart body) :: environment) body smaller term := by
  simp only [evaluate]
  apply BinderBudgetLanguage.mu_unfold
  intro before after included
  apply evaluate_mono holds body
  intro index
  cases index with
  | zero => exact included
  | succ index => exact fun _ _ accepted => accepted

end MicroCFTA.InternedGuardedBudgetSyntax
