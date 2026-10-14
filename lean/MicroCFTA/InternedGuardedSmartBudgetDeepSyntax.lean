import MicroCFTA.InternedGuardedSmartBudgetDeepSupport

/-!
# Complete lexical root inclusion and deep support

Nodes have no literal roots. Retained Mu binders also have no literal roots.
Their complete support law therefore supplies deep support. Unions and
removed smart binders retain the separate root and deep relations.
-/
namespace MicroCFTA.InternedGuardedSmartBudgetSupport
open Language InternedNestedConstruction
open InternedDepthSemantics (Shape)
open BinderBudgetLanguage (Lang)

/-- A combined shape's literal root comes from one original operand. -/
theorem combined_roots (shapes : List (Shape Atom)) (name : Atom) :
    name ∈ (InternedDepthSemantics.combineMany shapes).roots ↔ ∃ shape ∈ shapes, name ∈ shape.roots := by
  induction shapes with
  | nil => simp only [InternedDepthSemantics.combineMany, List.not_mem_nil, false_and, exists_false]
  | cons first rest ih =>
      simp only [InternedDepthSemantics.combineMany, InternedDepthSemantics.combine, List.mem_append,
        ih, List.mem_cons, exists_eq_or_imp]

/-- A combined shape's deep name comes from one original operand. -/
theorem combined_deep (shapes : List (Shape Atom)) (name : Atom) :
    name ∈ (InternedDepthSemantics.combineMany shapes).deep ↔ ∃ shape ∈ shapes, name ∈ shape.deep := by
  induction shapes with
  | nil => simp only [InternedDepthSemantics.combineMany, List.not_mem_nil, false_and, exists_false]
  | cons first rest ih =>
      simp only [InternedDepthSemantics.combineMany, InternedDepthSemantics.combine, List.mem_append,
        ih, List.mem_cons, exists_eq_or_imp]

/-- Each lexical input has exact literal root inclusion and deep budget support. -/
def DeepInputs (shapes : List (Shape Atom)) (before after : Atom → Lang Symbol) (left right : List (Lang Symbol)) : Prop :=
  ∀ index : Nat, DeepRelated (shapes[index]?.getD {}) before after
    (left[index]?.getD (fun _ _ => False)) (right[index]?.getD (fun _ _ => False))

/-- A symbolic binder retains deep support for its local and each captured input. -/
theorem deep_inputs_binder (shapes : List (Shape Atom)) (before after : Atom → Lang Symbol) (left right : List (Lang Symbol))
    (inputs : DeepInputs shapes before after left right) (leftCandidate rightCandidate : Lang Symbol) :
    DeepInputs (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr))
      (extend before leftCandidate) (extend after rightCandidate) (leftCandidate :: left) (rightCandidate :: right) := by
  intro index
  cases index with
  | zero => exact deep_local before after leftCandidate rightCandidate
  | succ index =>
      have lifted := deep_lift before after leftCandidate rightCandidate _ _ _ (inputs index)
      have lookup := InternedGuardedSyntaxSupport.map_getD shapes (Shape.map (Sum.inr : Atom → Sum Unit Atom)) {} index
      have lookupEmpty : (shapes.map (Shape.map (Sum.inr : Atom → Sum Unit Atom)))[index]?.getD {} =
          (shapes[index]?.getD {}).map Sum.inr := by simpa only [Shape.map, List.map_nil] using lookup
      simpa only [List.getElem?_cons_succ, lookupEmpty] using lifted

/-- Complete smart syntax includes its literal roots and confines other ambient changes to deep names. -/
theorem evaluate_deep {Atom : Type} (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (shapes : List (Shape Atom)) (before after : Atom → Lang Symbol) (left right : List (Lang Symbol))
    (inputs : DeepInputs shapes before after left right) :
    DeepRelated (InternedDepthSemantics.evaluate expression shapes) before after
      (InternedGuardedSmartBudget.evaluate holds shapes left expression) (InternedGuardedSmartBudget.evaluate holds shapes right expression) := by
  have base := evaluate_related holds expression shapes before after left right (fun index => (inputs index).toRelated)
  cases expression with
  | empty => exact deep_rootless _ _ _ _ _ base (by rw [InternedDepthSemantics.evaluate])
  | var index => simpa only [InternedDepthSemantics.evaluate, InternedGuardedSmartBudget.evaluate] using inputs index
  | node edges =>
      apply deep_rootless _ _ _ _ _ base
      rw [InternedDepthSemantics.evaluate, InternedDepthSemanticProjections.edges_roots]
  | union members =>
      have each (member : Syntax Symbol Guard) (present : member ∈ members) := by
        have smaller := List.sizeOf_lt_of_mem present
        exact evaluate_deep holds member shapes before after left right inputs
      refine ⟨base, ?_, ?_, ?_⟩
      · rintro budget term ⟨name, member, accepted⟩
        rw [InternedDepthSemantics.evaluate, combined_roots, shapes_many] at member
        obtain ⟨selected, present, named⟩ := member
        obtain ⟨expression, inMembers, rfl⟩ := List.mem_map.mp present
        rw [InternedGuardedSmartBudget.evaluate]
        exact ⟨⟨expression, inMembers⟩, (each expression inMembers).root_left budget term ⟨name, named, accepted⟩⟩
      · rintro budget term ⟨name, member, accepted⟩
        rw [InternedDepthSemantics.evaluate, combined_roots, shapes_many] at member
        obtain ⟨selected, present, named⟩ := member
        obtain ⟨expression, inMembers, rfl⟩ := List.mem_map.mp present
        rw [InternedGuardedSmartBudget.evaluate]
        exact ⟨⟨expression, inMembers⟩, (each expression inMembers).root_right budget term ⟨name, named, accepted⟩⟩
      · intro agree budget term accepted
        rw [InternedGuardedSmartBudget.evaluate] at accepted
        obtain ⟨⟨expression, inMembers⟩, accepted⟩ := accepted
        have innerAgree : Agree before after (InternedDepthSemantics.evaluate expression shapes).deep := by
          intro name member
          apply agree name
          rw [InternedDepthSemantics.evaluate, combined_deep, shapes_many]
          exact ⟨_, List.mem_map.mpr ⟨expression, inMembers, rfl⟩, member⟩
        rcases (each expression inMembers).deep_change innerAgree budget term accepted with accepted | ⟨name, member, accepted⟩
        · left
          rw [InternedGuardedSmartBudget.evaluate]
          exact ⟨⟨expression, inMembers⟩, accepted⟩
        · right
          refine ⟨name, ?_, accepted⟩
          rw [InternedDepthSemantics.evaluate, combined_roots, shapes_many]
          exact ⟨_, List.mem_map.mpr ⟨expression, inMembers, rfl⟩, member⟩
  | binder smart body =>
      have bodyRelated (leftCandidate rightCandidate : Lang Symbol) :=
        evaluate_deep holds body (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr))
          (extend before leftCandidate) (extend after rightCandidate) (leftCandidate :: left) (rightCandidate :: right)
          (deep_inputs_binder shapes before after left right inputs leftCandidate rightCandidate)
      simpa only [InternedDepthSemantics.evaluate, InternedGuardedSmartBudget.evaluate] using
        deep_binder before after smart _ _ _ bodyRelated
termination_by sizeOf expression
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

end MicroCFTA.InternedGuardedSmartBudgetSupport
