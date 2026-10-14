import MicroCFTA.InternedGuardedSmartBudget

/-!
# External names do not change lexical smart budgets

The existing shape interpreter commutes with every external-name map.
Such maps preserve deep local occurrences. The budget interpretation
therefore makes the same smart decision before and after renaming.
-/
namespace MicroCFTA.InternedGuardedSmartBudget
open InternedNestedConstruction Language
open InternedDepthSemantics (Shape)
open BinderBudgetLanguage (Lang)

mutual
/-- Arbitrary external shape renaming retains each complete lexical budget language. -/
theorem evaluate_map {Atom Other : Type} (function : Atom → Other) (holds : Guard → Term Symbol → Bool)
    (expression : Syntax Symbol Guard) (shapes : List (Shape Atom)) (environment : List (Lang Symbol)) :
    evaluate holds (shapes.map (Shape.map function)) environment expression = evaluate holds shapes environment expression := by
  cases expression with
  | empty | var => rw [evaluate, evaluate]
  | node edges =>
      rw [evaluate, evaluate]
      funext budget term
      apply propext
      apply exists_congr
      intro edge
      exact iff_of_eq (congrFun (congrFun (edgeMeaning_map function holds edge.val shapes environment) budget) term)
  | union members =>
      rw [evaluate, evaluate]
      funext budget term
      apply propext
      apply exists_congr
      intro member
      exact iff_of_eq (congrFun (congrFun (evaluate_map function holds member.val shapes environment) budget) term)
  | binder smart body =>
      have bodyShape := InternedDepthSemantics.evaluate_map (Sum.map id function) body
        (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr))
      rw [InternedDepthSemantics.local_map function shapes] at bodyShape
      rw [evaluate, evaluate]
      simp only [bodyShape, Shape.map, InternedDepthSemantics.hasLocal_map]
      split
      · apply congrArg BinderBudgetLanguage.mu
        funext language
        have mapped := evaluate_map (Sum.map id function) holds body
          (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr)) (language :: environment)
        rw [InternedDepthSemantics.local_map function shapes] at mapped
        exact mapped
      · have mapped := evaluate_map (Sum.map id function) holds body
          (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr)) ((fun _ _ => False) :: environment)
        rw [InternedDepthSemantics.local_map function shapes] at mapped
        exact mapped
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- External shape renaming retains complete edge guards and ordered child budgets. -/
theorem edgeMeaning_map {Atom Other : Type} (function : Atom → Other) (holds : Guard → Term Symbol → Bool)
    (edge : EdgeSyntax Symbol Guard) (shapes : List (Shape Atom)) (environment : List (Lang Symbol)) :
    edgeMeaning holds (shapes.map (Shape.map function)) environment edge = edgeMeaning holds shapes environment edge := by
  cases edge with
  | mk symbol guard children =>
      rw [edgeMeaning, edgeMeaning]
      funext budget term
      apply propext
      exact exists_congr (fun terms => and_congr Iff.rfl
        (and_congr (forest_map function holds children terms shapes environment budget) Iff.rfl))
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- External shape renaming retains the exact common-budget ordered forest relation. -/
theorem forest_map {Atom Other : Type} (function : Atom → Other) (holds : Guard → Term Symbol → Bool)
    (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol)) (shapes : List (Shape Atom))
    (environment : List (Lang Symbol)) (budget : Nat) :
    forest holds (shapes.map (Shape.map function)) environment budget children terms ↔
      forest holds shapes environment budget children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest]
  | cons child rest =>
      cases terms with
      | nil => simp only [forest]
      | cons term terms =>
          rw [forest, forest, evaluate_map function holds child shapes environment]
          exact and_congr Iff.rfl (forest_map function holds rest terms shapes environment budget)
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

end MicroCFTA.InternedGuardedSmartBudget
