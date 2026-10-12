import MicroCFTA.InternedNestedDependencies

/-!
# Lexical scope bounds the exact source input inventory

The original scope check bounds every collected input slot. A closed
expression therefore has no enclosing input dependency. No executed record
or successful source computation is required for this conclusion.
-/
namespace MicroCFTA.InternedNestedDependencies
open InternedNestedConstruction

mutual
/-- Every source input slot belongs to the expression's declared enclosing scope. -/
theorem inputs_bounded (expression : Syntax Symbol Guard) (depth : Nat) (scope : Scoped depth expression) :
    ∀ index ∈ inputs expression, index < depth := by
  cases expression with
  | empty => simp [inputs]
  | var selected =>
      intro index member
      have same : index = selected := by simpa only [inputs, List.mem_singleton] using member
      simpa only [same, Scoped] using scope
  | node edges => simpa only [inputs] using edgeInputs_bounded edges depth (by simpa only [Scoped] using scope)
  | union members => simpa only [inputs] using manyInputs_bounded members depth (by simpa only [Scoped] using scope)
  | binder smart body =>
      simp only [Scoped] at scope
      intro index member
      simp only [inputs] at member
      obtain ⟨original, present, selected⟩ := List.mem_filterMap.mp member
      cases original with
      | zero => cases selected
      | succ previous =>
          have same : previous = index := Option.some.inj selected
          have bounded := inputs_bounded body (depth + 1) scope (previous + 1) present
          omega
termination_by sizeOf expression

/-- Every ordered child dependency belongs to the same original lexical scope. -/
theorem manyInputs_bounded (expressions : List (Syntax Symbol Guard)) (depth : Nat)
    (scope : ManyScoped depth expressions) : ∀ index ∈ manyInputs expressions, index < depth := by
  cases expressions with
  | nil => simp [manyInputs]
  | cons first rest =>
      simp only [ManyScoped] at scope
      intro index member
      simp only [manyInputs, List.mem_append] at member
      rcases member with head | tail
      · exact inputs_bounded first depth scope.1 index head
      · exact manyInputs_bounded rest depth scope.2 index tail
termination_by sizeOf expressions

/-- Source edge declarations add only their actual child dependencies. -/
theorem edgeInputs_bounded (expressions : List (EdgeSyntax Symbol Guard)) (depth : Nat)
    (scope : EdgesScoped depth expressions) : ∀ index ∈ edgeInputs expressions, index < depth := by
  cases expressions with
  | nil => simp [edgeInputs]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesScoped] at scope
          intro index member
          simp only [edgeInputs, List.mem_append] at member
          rcases member with head | tail
          · exact manyInputs_bounded children depth scope.1 index head
          · exact edgeInputs_bounded rest depth scope.2 index tail
termination_by sizeOf expressions
end

/-- Lexically closed source syntax is independent of every enclosing callback input. -/
theorem closed_inputs (expression : Syntax Symbol Guard) (scope : Scoped 0 expression) : inputs expression = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro index member
  exact Nat.not_lt_zero index (inputs_bounded expression 0 scope index member)

end MicroCFTA.InternedNestedDependencies
