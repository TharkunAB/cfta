import MicroCFTA.UnionDiagonalRowBoundary
import MicroCFTA.DirectionalProduct

/-!
# Directional coverage proves the retained union witness

Product-to-result projection covers every redundant cross row. The reverse
proof copies original ordinary rows into the product. Both local proofs are
structural. The earlier exact-child relation is still impossible.
-/
namespace MicroCFTA.UnionDiagonalRowCoverage
open Language SymbolicGraphView DirectionalRows UnionDiagonalRowBoundary

/-- Every product row is covered by the original right operand through ordered child inclusion. -/
theorem forward_rows : Simulation (DiagonalProduct.graph source) source (fun pair state => pair.2 = state) :=
  DirectionalProduct.project_right source

/-- The ordinary source rows occur literally in the source union, so diagonal copies give reverse coverage. -/
theorem reverse_rows : Simulation source (DiagonalProduct.graph source) (fun state pair =>
    pair = (state, state) ∨ state = 1 ∧ pair = (0, 1)) := by
  apply DirectionalProduct.copy_into_right source 0 1
  intro edge member
  have rows : source 0 = source 1 ++ [row 4 [4]] := rfl
  rw [rows]
  exact List.mem_append_left _ member

/-- Separate local row simulations prove the full correct output language for the witness. -/
theorem covered_language (term : Term Nat) :
    Accepts source 1 term ↔ Accepts (DiagonalProduct.graph source) (0, 1) term :=
  DirectionalRows.language_exact _ _ _ _ forward_rows reverse_rows (0, 1) 1 rfl (Or.inr ⟨rfl, rfl⟩) term

/-- Directional coverage is strictly more general than the exact related-row interface on this explicit graph. -/
theorem no_exact_relation : ¬ ∃ related : (Fin 6 × Fin 6) → Fin 6 → Prop,
    related (0, 1) 1 ∧ RelatedRows.Readback (DiagonalProduct.graph source) source related := by
  rintro ⟨related, root, view⟩
  exact no_related_readback related root view

end MicroCFTA.UnionDiagonalRowCoverage
