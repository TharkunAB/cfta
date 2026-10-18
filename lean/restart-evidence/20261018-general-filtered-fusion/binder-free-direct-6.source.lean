import MicroCFTA.SourceCurrentFilteredNodeFusion
import MicroCFTA.SourceCurrentFilteredUnionFusion
import MicroCFTA.InternedStoredShallowCompletion

/-!
# Complete filtered Empty fusion without source binders

The source expression can use empty values, variables, nodes and unions.
Its supplied fixed captures can contain open nested Mu values. Their free
replacement bindings must agree, as required by the common Fusion law.
The result does not cover new source binder expressions.
-/
namespace MicroCFTA.SourceCurrentFilteredBinderFreeFusion
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open SourceCurrentFilteredSourceFusion (Fusion)

private theorem member_free (expressions : List (Syntax Symbol Guard))
    (free : ManyBinderFree expressions) (child : Syntax Symbol Guard) (member : child ∈ expressions) :
    BinderFree child := by
  induction expressions with
  | nil => cases member
  | cons first rest ih =>
      rw [ManyBinderFree] at free
      rcases List.mem_cons.mp member with rfl | member
      · exact free.1
      · exact ih free.2 member

private theorem row_free (rows : List (EdgeSyntax Symbol Guard))
    (free : EdgesBinderFree rows) (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (member : EdgeSyntax.mk symbol guard children ∈ rows) : ManyBinderFree children := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk own ownGuard ownChildren =>
          rw [EdgesBinderFree] at free
          rcases List.mem_cons.mp member with equal | member
          · cases equal; exact free.1
          · exact ih free.2 member

/-- Every binder-free source expression satisfies actual reader-filtered Empty fusion. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (free : BinderFree expression) : Fusion expression := by
  generalize measure : sizeOf expression = bound
  induction bound using Nat.strongRecOn generalizing expression with
  | ind bound ih =>
      cases expression with
      | empty => exact SourceCurrentFilteredSourceFusion.empty
      | var index => exact SourceCurrentFilteredSourceFusion.reference index
      | binder => simp only [BinderFree] at free
      | union expressions =>
          rw [BinderFree] at free
          apply SourceCurrentFilteredUnionFusion.union expressions
          intro child member
          have smaller : sizeOf child < bound := by
            have inside := List.sizeOf_lt_of_mem member
            simp only [Syntax.union.sizeOf_spec] at measure
            omega
          exact ih (sizeOf child) smaller child (member_free expressions free child member) rfl
      | node rows =>
          rw [BinderFree] at free
          apply SourceCurrentFilteredNodeFusion.node rows
          intro symbol guard children member child included
          have smaller : sizeOf child < bound := by
            have outer := List.sizeOf_lt_of_mem member
            have inner := List.sizeOf_lt_of_mem included
            simp only [Syntax.node.sizeOf_spec] at measure
            simp only [EdgeSyntax.mk.sizeOf_spec] at outer
            omega
          exact ih (sizeOf child) smaller child
            (member_free children (row_free rows free symbol guard children member) child included) rfl

end MicroCFTA.SourceCurrentFilteredBinderFreeFusion
