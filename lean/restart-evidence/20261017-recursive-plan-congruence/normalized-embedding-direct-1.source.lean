import MicroCFTA.SourceCurrentNormalizedPlanRelation

/-!
# Ordered plans embed into recursively normalized plans

Ordered equivalent plans retain their original child and union order.
Each paired node row supplies a witness in both directions of the
normalized row relation. The proof also covers nested binder bodies.
-/
namespace MicroCFTA.SourceCurrentNormalizedPlanEmbedding
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryPlanEquivalence
open SourceCurrentNormalizedPlanRelation

mutual
/-- Ordered equivalent plans satisfy the recursive normalized relation. -/
theorem equivalent (first : Syntax Symbol Guard) (firstInputs : List (Value Symbol Guard))
    (second : Syntax Symbol Guard) (secondInputs : List (Value Symbol Guard))
    (paired : Equivalent first firstInputs second secondInputs) :
    Related first firstInputs second secondInputs := by
  cases first <;> cases second <;> simp only [Equivalent] at paired <;> try contradiction
  case empty.empty => trivial
  case var.var left right => exact paired
  case node.node left right => exact edges_equivalent left firstInputs right secondInputs paired
  case union.union left right => exact many_equivalent left firstInputs right secondInputs paired
  case binder.binder firstSmart left secondSmart right =>
    exact ⟨paired.1, fun name => equivalent left (.reference name :: firstInputs)
      right (.reference name :: secondInputs) (paired.2 name)⟩
termination_by sizeOf first

/-- Ordered child and union lists retain every paired member. -/
theorem many_equivalent (first : List (Syntax Symbol Guard)) (firstInputs : List (Value Symbol Guard))
    (second : List (Syntax Symbol Guard)) (secondInputs : List (Value Symbol Guard))
    (paired : ManyEquivalent first firstInputs second secondInputs) :
    ManyRelated first firstInputs second secondInputs := by
  cases first <;> cases second <;> simp only [ManyEquivalent] at paired <;> try contradiction
  case nil.nil => trivial
  case cons.cons left rest right remaining =>
    exact ⟨equivalent left firstInputs right secondInputs paired.1,
      many_equivalent rest firstInputs remaining secondInputs paired.2⟩
termination_by sizeOf first

/-- Each ordered equivalent row supplies both normalized occurrence witnesses. -/
theorem edges_equivalent (first : List (EdgeSyntax Symbol Guard)) (firstInputs : List (Value Symbol Guard))
    (second : List (EdgeSyntax Symbol Guard)) (secondInputs : List (Value Symbol Guard))
    (paired : EdgesEquivalent first firstInputs second secondInputs) :
    RowsRelated first firstInputs second secondInputs := by
  cases first <;> cases second <;> try cases paired
  case nil.nil => exact ⟨fun _ impossible => False.elim (List.not_mem_nil impossible),
    fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  case nil.cons row rest => cases row; simp only [EdgesEquivalent] at paired
  case cons.nil row rest => cases row; simp only [EdgesEquivalent] at paired
  case cons.cons row rest other remaining =>
    cases row with
    | mk symbol guard children =>
        cases other with
        | mk otherSymbol otherGuard otherChildren =>
            have child := many_equivalent children firstInputs otherChildren secondInputs paired.2.2.1
            have tail := edges_equivalent rest firstInputs remaining secondInputs paired.2.2.2
            have head : RowRelated (.mk symbol guard children) firstInputs
                (.mk otherSymbol otherGuard otherChildren) secondInputs := ⟨paired.1, paired.2.1, child⟩
            constructor
            · intro selected member
              rcases List.mem_cons.mp member with rfl | later
              · exact ⟨_, List.mem_cons_self, head⟩
              · obtain ⟨output, present, related⟩ := tail.1 selected later
                exact ⟨output, List.mem_cons_of_mem _ present, related⟩
            · intro selected member
              rcases List.mem_cons.mp member with rfl | later
              · exact ⟨_, List.mem_cons_self, head⟩
              · obtain ⟨output, present, related⟩ := tail.2 selected later
                exact ⟨output, List.mem_cons_of_mem _ present, related⟩
termination_by sizeOf first
end

end MicroCFTA.SourceCurrentNormalizedPlanEmbedding
