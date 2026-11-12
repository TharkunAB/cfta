import MicroCFTA.SourceSynthesisTypeSyntax
import Init.Data.List.Perm

/-!
# Original query tokens from a name permutation

The proof retains each original name and type pair.
It preserves duplicate occurrences and does not canonicalize their type fields.
It requires no injectivity or distinct-name condition.
-/
namespace MicroCFTA.SourceSynthesisQueryTokenPermutation
open SourceSynthesisTypeSyntax (Ty Query)

private theorem lift_map_permutation {α β : Type} (f : α → β)
    (names : List β) (source : List α) (permuted : names.Perm (source.map f)) :
    ∃ tokens : List α, tokens.Perm source ∧ tokens.map f = names := by
  induction names generalizing source with
  | nil =>
      have sourceEmpty : source = [] := List.eq_nil_of_map_eq_nil permuted.symm.eq_nil
      subst source
      exact ⟨[], .refl [], rfl⟩
  | cons name names ih =>
      have present : name ∈ source.map f := permuted.subset List.mem_cons_self
      obtain ⟨entry, included, found⟩ := List.mem_map.mp present
      obtain ⟨before, after, sourceEq⟩ := List.append_of_mem included
      have moved : source.Perm (entry :: (before ++ after)) := by
        rw [sourceEq]
        exact List.perm_middle
      have aligned : (name :: names).Perm (name :: (before ++ after).map f) := by
        have mapped := permuted.trans (moved.map f)
        simpa only [List.map_cons, found] using mapped
      obtain ⟨rest, remaining, mappedRest⟩ := ih (before ++ after) aligned.cons_inv
      refine ⟨entry :: rest, (remaining.cons entry).trans moved.symm, ?_⟩
      simp only [List.map_cons, found, mappedRest]

/-- Every permutation of original query names retains an occurrence-preserving token witness. -/
theorem original_tokens (query : Query) (names : List String)
    (permuted : names.Perm (query.queryArguments.map Prod.fst)) :
    ∃ tokens : List (String × Ty), tokens.Perm query.queryArguments ∧ tokens.map Prod.fst = names :=
  lift_map_permutation Prod.fst names query.queryArguments permuted

end MicroCFTA.SourceSynthesisQueryTokenPermutation
