import MicroCFTA.InternedGuardedLanguage

/-!
# Independent guarded meaning of the actual lexical source plans

Lexical variables read languages by position. Both binder forms denote the
least language of the body with one new local. Constructor syntax retains
each source guard and ordered child plan.
-/
namespace MicroCFTA.InternedGuardedSyntax
open InternedNestedConstruction Language
open BinderLanguage (Lang Included least)

mutual
/-- Interpret every lexical source branch by its intended guarded least language. -/
def evaluate (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol)) : Syntax Symbol Guard → Lang Symbol
  | .empty => fun _ => False
  | .var index => environment[index]?.getD (fun _ => False)
  | .node edges => fun term => ∃ edge : {edge // edge ∈ edges}, edgeMeaning holds environment edge.val term
  | .union members => fun term => ∃ member : {member // member ∈ members}, evaluate holds environment member.val term
  | .binder _ body => least (fun language => evaluate holds (language :: environment) body)
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Interpret a full guarded source edge and its ordered child plans. -/
def edgeMeaning (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol)) : EdgeSyntax Symbol Guard → Lang Symbol
  | .mk symbol guard children => fun term => ∃ terms, term = .node symbol terms ∧
      forest holds environment children terms ∧ holds guard term = true
termination_by edge => sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Interpret exactly the ordered finite forest of lexical source children. -/
def forest (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol)) :
    List (Syntax Symbol Guard) → List (Term Symbol) → Prop
  | [], [] => True
  | child :: rest, term :: terms => evaluate holds environment child term ∧ forest holds environment rest terms
  | _, _ => False
termination_by children _ => sizeOf children
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- Every source plan is positive in each lexical input language. -/
theorem evaluate_mono (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ => False)) (after[index]?.getD (fun _ => False))) :
    Included (evaluate holds before expression) (evaluate holds after expression) := by
  cases expression with
  | empty => rw [evaluate, evaluate]; exact fun _ impossible => impossible
  | var index => simpa only [evaluate] using included index
  | node edges =>
      rw [evaluate, evaluate]
      rintro term ⟨edge, accepted⟩
      exact ⟨edge, edgeMeaning_mono holds edge.val before after included term accepted⟩
  | union members =>
      rw [evaluate, evaluate]
      rintro term ⟨member, accepted⟩
      exact ⟨member, evaluate_mono holds member.val before after included term accepted⟩
  | binder smart body =>
      rw [evaluate, evaluate]
      apply BinderLanguage.least_mono
      intro language
      apply evaluate_mono holds body
      intro index
      cases index with
      | zero => exact fun _ accepted => accepted
      | succ index => exact included index
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Full guarded edge plans preserve lexical-language inclusion. -/
theorem edgeMeaning_mono (holds : Guard → Term Symbol → Bool) (edge : EdgeSyntax Symbol Guard)
    (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ => False)) (after[index]?.getD (fun _ => False))) :
    Included (edgeMeaning holds before edge) (edgeMeaning holds after edge) := by
  cases edge with
  | mk symbol guard children =>
      rw [edgeMeaning, edgeMeaning]
      rintro term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_mono holds children terms before after included runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordered source child plans preserve lexical-language inclusion. -/
theorem forest_mono (holds : Guard → Term Symbol → Bool) (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol))
    (before after : List (Lang Symbol))
    (included : ∀ index : Nat, Included (before[index]?.getD (fun _ => False)) (after[index]?.getD (fun _ => False)))
    (accepted : forest holds before children terms) : forest holds after children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [forest] at accepted
      | cons term terms =>
          rw [forest] at accepted ⊢
          exact ⟨evaluate_mono holds child before after included term accepted.1,
            forest_mono holds rest terms before after included accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals simp_all only; all_goals simp_wf; all_goals omega
end

/-- Both source binder forms satisfy their intended least-language unfolding equation. -/
theorem binder_unfold (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol))
    (smart : Bool) (body : Syntax Symbol Guard) (term : Term Symbol) :
    evaluate holds environment (.binder smart body) term ↔
      evaluate holds (evaluate holds environment (.binder smart body) :: environment) body term := by
  simp only [evaluate]
  apply BinderLanguage.least_fix
  intro before after included
  apply evaluate_mono holds body
  intro index
  cases index with
  | zero => exact included
  | succ index => exact fun _ accepted => accepted

end MicroCFTA.InternedGuardedSyntax
