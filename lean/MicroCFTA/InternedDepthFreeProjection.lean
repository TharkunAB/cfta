import MicroCFTA.InternedDepthSemanticProjections

/-!
# Free-name membership of the full depth interpreter

Shape union groups root and deep occurrences separately. Its free-name list
can therefore differ in order from the existing free-name interpreter.
Membership agrees through all source syntax, including both binder forms.
-/
namespace MicroCFTA.InternedDepthFreeProjection
open InternedNestedConstruction InternedDepthSemantics InternedDepthSemanticProjections

/-- Shape union preserves the union of free-name memberships. -/
theorem combine_member (first second : Shape Atom) (name : Atom) :
    name ∈ (combine first second).free ↔ name ∈ first.free ∨ name ∈ second.free := by
  simp only [Shape.free, combine, List.mem_append]
  simp only [or_assoc, or_left_comm]

/-- The empty shape contributes no free name. -/
theorem empty_free : ({} : Shape Atom).free = [] := rfl

/-- Both binder forms remove exactly the fresh symbolic local from free names. -/
theorem binder_free (smart : Bool) (body : Shape (Sum Unit Atom)) :
    (binder smart body).free = InternedFreeNameSemantics.lower body.free := by
  unfold binder
  split
  · rfl
  · simp only [Shape.free, lower, InternedFreeNameSemantics.lower, List.filterMap_append]

/-- Encoding external names maps the complete free-name list. -/
theorem map_free (function : Atom → Other) (value : Shape Atom) :
    (value.map function).free = value.free.map function := by
  simp only [Shape.map, Shape.free, List.map_append]

/-- The local shape environment projects to the existing free-name environment. -/
theorem free_local (environment : List (Shape Atom)) :
    (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)).map Shape.free =
      [Sum.inl ()] :: (environment.map Shape.free).map (List.map Sum.inr) := by
  simp only [List.map_cons, List.map_map, Function.comp_def, map_free]
  rfl

/-- Profile projection gives exactly the source edge survival test. -/
theorem children_live (children : List (Shape Atom)) :
    (children.map profile).all (fun child => !InternedProfileSemantics.isEmpty child) =
      !children.any Shape.isEmpty := by
  rw [List.all_map]
  simp only [Function.comp_def, profile_empty]
  exact (List.not_any_eq_all_not).symm

/-- A surviving ordinary edge retains every child free name below its boundary. -/
theorem edge_free (children : List (Shape Atom)) :
    (edge children).free =
      if (children.map profile).all (fun child => !InternedProfileSemantics.isEmpty child)
      then (combineMany children).free else [] := by
  rw [children_live]
  cases live : children.any Shape.isEmpty <;> simp [edge, live, Shape.free]

mutual
/-- The complete depth/deep interpreter has exactly the existing free-name membership. -/
theorem evaluate_member {Atom : Type} (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (valid : CoherentMany environment) (name : Atom) :
    name ∈ (evaluate expression environment).free ↔
      name ∈ InternedFreeNameSemantics.evaluate expression (environment.map profile) (environment.map Shape.free) := by
  cases expression with
  | empty => simp only [evaluate, empty_free, InternedFreeNameSemantics.evaluate]
  | var index =>
    rw [evaluate, InternedFreeNameSemantics.evaluate]
    cases found : environment[index]? <;> simp [List.getElem?_map, found, Shape.free]
  | node edges =>
    simpa only [evaluate, InternedFreeNameSemantics.evaluate] using evaluateEdges_member edges environment valid name
  | union members =>
    simpa only [evaluate, InternedFreeNameSemantics.evaluate] using evaluateMany_member members environment valid name
  | binder smart body =>
    rw [evaluate, binder_free, InternedFreeNameSemantics.evaluate, InternedFreeNameSemantics.lower_member,
      InternedFreeNameSemantics.lower_member]
    rw [←profile_local environment, ←free_local environment]
    exact evaluate_member body _ (local_coherent environment valid) (.inr name)
termination_by sizeOf expression

/-- Combining all shape operands and flattening old free-name operands preserve the same members. -/
theorem evaluateMany_member {Atom : Type} (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom))
    (valid : CoherentMany environment) (name : Atom) :
    name ∈ (combineMany (evaluateMany expressions environment)).free ↔
      name ∈ (InternedFreeNameSemantics.evaluateMany expressions (environment.map profile) (environment.map Shape.free)).flatten := by
  cases expressions with
  | nil => simp only [evaluateMany, combineMany, empty_free, InternedFreeNameSemantics.evaluateMany, List.flatten_nil]
  | cons first rest =>
    simp only [evaluateMany, combineMany, combine_member, InternedFreeNameSemantics.evaluateMany,
      List.flatten_cons, List.mem_append, evaluate_member first environment valid name,
      evaluateMany_member rest environment valid name]
termination_by sizeOf expressions

/-- Deleted edges contribute no names; every surviving source edge has the same membership. -/
theorem evaluateEdges_member {Atom : Type} (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom))
    (valid : CoherentMany environment) (name : Atom) :
    name ∈ (evaluateEdges expressions environment).free ↔
      name ∈ InternedFreeNameSemantics.evaluateEdges expressions (environment.map profile) (environment.map Shape.free) := by
  cases expressions with
  | nil => simp only [evaluateEdges, empty_free, InternedFreeNameSemantics.evaluateEdges]
  | cons first rest =>
    cases first with
    | mk symbol guard children =>
      rw [evaluateEdges, combine_member, edge_free, evaluateMany_profile children environment valid,
        InternedFreeNameSemantics.evaluateEdges, List.mem_append, evaluateEdges_member rest environment valid name]
      apply or_congr_left
      split <;> simp only [evaluateMany_member children environment valid name, iff_self]
termination_by sizeOf expressions
end

end MicroCFTA.InternedDepthFreeProjection
