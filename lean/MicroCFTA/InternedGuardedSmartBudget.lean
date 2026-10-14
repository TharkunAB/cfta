import MicroCFTA.InternedGuardedBudget
import MicroCFTA.InternedDepthSemantics

/-!
# Guarded lexical budgets with the actual smart cleanup decision

The existing depth shapes decide whether a local occurs deeply. Raw binders
and smart binders with a deep local consume one step. Other smart binders
evaluate their body with an empty local language. Source correspondence
requires the actual record and probe invariants.
-/
namespace MicroCFTA.InternedGuardedSmartBudget
open InternedNestedConstruction Language
open InternedDepthSemantics (Shape)
open BinderBudgetLanguage (Lang Included Upward)

mutual
/-- Interpret complete lexical syntax with its existing deep-local cleanup decision. -/
def evaluate {Atom : Type} (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom))
    (environment : List (Lang Symbol)) : Syntax Symbol Guard → Lang Symbol
  | .empty => fun _ _ => False
  | .var index => environment[index]?.getD (fun _ _ => False)
  | .node edges => fun budget term => ∃ edge : {edge // edge ∈ edges}, edgeMeaning holds shapes environment edge.val budget term
  | .union members => fun budget term => ∃ member : {member // member ∈ members}, evaluate holds shapes environment member.val budget term
  | .binder smart body =>
      let innerShapes := (⟨[Sum.inl ()], [], false, 0⟩ : Shape (Sum Unit Atom)) :: shapes.map (Shape.map Sum.inr)
      if !smart || InternedDepthSemantics.hasLocal (InternedDepthSemantics.evaluate body innerShapes).deep then
        BinderBudgetLanguage.mu (fun language => evaluate holds innerShapes (language :: environment) body)
      else evaluate holds innerShapes ((fun _ _ => False) :: environment) body
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Complete lexical edges retain their guards and common child budget. -/
def edgeMeaning {Atom : Type} (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom))
    (environment : List (Lang Symbol)) : EdgeSyntax Symbol Guard → Lang Symbol
  | .mk symbol guard children => fun budget term => ∃ terms, term = .node symbol terms ∧
      forest holds shapes environment budget children terms ∧ holds guard term = true
termination_by edge => sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordered lexical children share one unfolding bound. -/
def forest {Atom : Type} (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom))
    (environment : List (Lang Symbol)) (budget : Nat) : List (Syntax Symbol Guard) → List (Term Symbol) → Prop
  | [], [] => True
  | child :: rest, term :: terms => evaluate holds shapes environment child budget term ∧ forest holds shapes environment budget rest terms
  | _, _ => False
termination_by children _ => sizeOf children
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- Each fixed shape environment gives a positive lexical budget interpretation. -/
theorem evaluate_mono {Atom : Type} (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (shapes : List (Shape Atom)) (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ _ => False)) (after[index]?.getD (fun _ _ => False))) :
    Included (evaluate holds shapes before expression) (evaluate holds shapes after expression) := by
  cases expression with
  | empty => rw [evaluate, evaluate]; exact fun _ _ impossible => impossible
  | var index => simpa only [evaluate] using included index
  | node edges =>
      rw [evaluate, evaluate]
      rintro budget term ⟨edge, accepted⟩
      exact ⟨edge, edgeMeaning_mono holds edge.val shapes before after included budget term accepted⟩
  | union members =>
      rw [evaluate, evaluate]
      rintro budget term ⟨member, accepted⟩
      exact ⟨member, evaluate_mono holds member.val shapes before after included budget term accepted⟩
  | binder smart body =>
      rw [evaluate, evaluate]
      split
      · apply BinderBudgetLanguage.mu_mono
        intro language
        apply evaluate_mono holds body
        intro index
        cases index with
        | zero => exact fun _ _ accepted => accepted
        | succ index => exact included index
      · apply evaluate_mono holds body
        intro index
        cases index with
        | zero => exact fun _ _ accepted => accepted
        | succ index => exact included index
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Full lexical edges retain input inclusion at each fixed unfolding bound. -/
theorem edgeMeaning_mono {Atom : Type} (holds : Guard → Term Symbol → Bool) (edge : EdgeSyntax Symbol Guard)
    (shapes : List (Shape Atom)) (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ _ => False)) (after[index]?.getD (fun _ _ => False))) :
    Included (edgeMeaning holds shapes before edge) (edgeMeaning holds shapes after edge) := by
  cases edge with
  | mk symbol guard children =>
      rw [edgeMeaning, edgeMeaning]
      rintro budget term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_mono holds children terms shapes before after included budget runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordered lexical forests retain input inclusion at their original common bound. -/
theorem forest_mono {Atom : Type} (holds : Guard → Term Symbol → Bool)
    (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol)) (shapes : List (Shape Atom))
    (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ _ => False)) (after[index]?.getD (fun _ _ => False)))
    (budget : Nat) (accepted : forest holds shapes before budget children terms) : forest holds shapes after budget children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [forest] at accepted
      | cons term terms =>
          rw [forest] at accepted ⊢
          exact ⟨evaluate_mono holds child shapes before after included budget term accepted.1,
            forest_mono holds rest terms shapes before after included budget accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

mutual
/-- Upward lexical inputs make every complete smart budget language upward. -/
theorem evaluate_upward {Atom : Type} (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (shapes : List (Shape Atom)) (environment : List (Lang Symbol))
    (upward : ∀ index : Nat, Upward (environment[index]?.getD (fun _ _ => False))) :
    Upward (evaluate holds shapes environment expression) := by
  cases expression with
  | empty => rw [evaluate]; exact fun _ _ _ _ impossible => impossible
  | var index => simpa only [evaluate] using upward index
  | node edges =>
      rw [evaluate]
      rintro before after bounded term ⟨edge, accepted⟩
      exact ⟨edge, edgeMeaning_upward holds edge.val shapes environment upward before after bounded term accepted⟩
  | union members =>
      rw [evaluate]
      rintro before after bounded term ⟨member, accepted⟩
      exact ⟨member, evaluate_upward holds member.val shapes environment upward before after bounded term accepted⟩
  | binder smart body =>
      rw [evaluate]
      split
      · exact BinderBudgetLanguage.mu_upward _
      · apply evaluate_upward holds body
        intro index
        cases index with
        | zero => exact fun _ _ _ _ impossible => impossible
        | succ index => exact upward index
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Upward lexical children make every complete guarded edge budget language upward. -/
theorem edgeMeaning_upward {Atom : Type} (holds : Guard → Term Symbol → Bool) (edge : EdgeSyntax Symbol Guard)
    (shapes : List (Shape Atom)) (environment : List (Lang Symbol))
    (upward : ∀ index : Nat, Upward (environment[index]?.getD (fun _ _ => False))) :
    Upward (edgeMeaning holds shapes environment edge) := by
  cases edge with
  | mk symbol guard children =>
      rw [edgeMeaning]
      rintro before after bounded term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_upward holds children terms shapes environment upward before after bounded runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Increasing the common unfolding bound retains every accepted lexical forest. -/
theorem forest_upward {Atom : Type} (holds : Guard → Term Symbol → Bool)
    (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol)) (shapes : List (Shape Atom))
    (environment : List (Lang Symbol)) (upward : ∀ index : Nat, Upward (environment[index]?.getD (fun _ _ => False)))
    (before after : Nat) (bounded : before ≤ after) (accepted : forest holds shapes environment before children terms) :
    forest holds shapes environment after children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [forest] at accepted
      | cons term terms =>
          rw [forest] at accepted ⊢
          exact ⟨evaluate_upward holds child shapes environment upward before after bounded term accepted.1,
            forest_upward holds rest terms shapes environment upward before after bounded accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

end MicroCFTA.InternedGuardedSmartBudget
