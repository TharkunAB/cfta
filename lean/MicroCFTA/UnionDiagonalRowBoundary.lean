import MicroCFTA.DiagonalProduct

/-!
# A self shortcut below a union requires directional row coverage

The common root language is exact, but one cross-product row has no exact
physical child representative in either retained target row. This excludes
even the nonfunctional exact related-row contract for the explicit graph.
The live source reproduction remains separate from verified extraction.
-/
namespace MicroCFTA.UnionDiagonalRowBoundary
open Language SymbolicGraphView

/-- Construct a complete unguarded row in the finite witness graph. -/
def row (symbol : Nat) (children : List (Fin 6)) : Edge (Fin 6) Nat := ⟨symbol, children, fun _ => true⟩

/-- Read union root 0, ordinary root 1, overlapping leaf sets 2 and 3, recursive branch 4, and enclosing root 5. -/
def source : Automaton (Fin 6) Nat := fun state =>
  if state = 0 then [row 3 [2], row 3 [3], row 4 [4]]
  else if state = 1 then [row 3 [2], row 3 [3]]
  else if state = 2 then [row 0 [], row 1 []]
  else if state = 3 then [row 1 [], row 2 []]
  else if state = 4 then [row 4 [4]]
  else [row 5 [0], row 5 [1]]

/-- Every retained ordinary root run is also a run at the source union root. -/
theorem ordinary_in_union (term : Term Nat) (accepted : Accepts source 1 term) : Accepts source 0 term := by
  have rows : source 0 = source 1 ++ [row 4 [4]] := rfl
  cases accepted with
  | node edge children member runs guard =>
      exact .node edge children (by rw [rows]; exact List.mem_append_left _ member) runs guard

/-- The returned original ordinary root has the full intended input-intersection language. -/
theorem full_root_language (term : Term Nat) :
    Accepts (DiagonalProduct.graph source) (0, 1) term ↔ Accepts source 1 term := by
  rw [DiagonalProduct.language_exact]
  exact ⟨And.right, fun accepted => ⟨ordinary_in_union term accepted, accepted⟩⟩

/-- The first leaf child accepts a while the second one rejects a. -/
theorem first_separates : Accepts source 2 (.node 0 []) ∧ ¬ Accepts source 3 (.node 0 []) := by
  constructor
  · exact .node (row 0 []) [] (by simp [source]) .nil rfl
  · rw [accepts_node_iff]
    simp [source, row]

/-- The second leaf child accepts c while the first one rejects c. -/
theorem second_separates : Accepts source 3 (.node 2 []) ∧ ¬ Accepts source 2 (.node 2 []) := by
  constructor
  · exact .node (row 2 []) [] (by simp [source]) .nil rfl
  · rw [accepts_node_iff]
    simp [source, row]

/-- Both source children accept b, so their cross-product row cannot be deleted as empty. -/
theorem common_leaf : Accepts (DiagonalProduct.graph source) (2, 3) (.node 1 []) := by
  apply (DiagonalProduct.language_exact source 2 3 _).mpr
  exact ⟨.node (row 1 []) [] (by simp [source]) .nil rfl,
    .node (row 1 []) [] (by simp [source]) .nil rfl⟩

/-- The source root product contains the live cross row with the proper common child language. -/
theorem cross_row : (⟨3, [(2, 3)], fun _ => true⟩ : Edge (Fin 6 × Fin 6) Nat) ∈ DiagonalProduct.graph source (0, 1) := by
  simp [DiagonalProduct.graph, source, row, Language.intersect, Language.intersectEdge]

/-- No exact related-row relation can describe this correct union result, even with multiple representatives. -/
theorem no_related_readback (related : (Fin 6 × Fin 6) → Fin 6 → Prop) (root : related (0, 1) 1) :
    ¬ RelatedRows.Readback (DiagonalProduct.graph source) source related := by
  intro view
  have exactChild := fun result paired term =>
    DiagonalProduct.related_product_exact source source related view 2 3 result paired term
  rcases view.complete (0, 1) 1 root ⟨3, [(2, 3)], fun _ => true⟩ cross_row with falseGuard | discarded | retained
  · have impossible := falseGuard (.node 1 [])
    cases impossible
  · obtain ⟨children, paired, child, member, empty⟩ := discarded
    cases children with
    | nil => cases paired
    | cons result rest =>
        cases paired with
        | cons head tail =>
            cases tail
            have same := List.mem_singleton.mp member
            subst child
            have accepted := (RelatedRows.language_exact _ _ related view (2, 3) result head (.node 1 [])).mpr common_leaf
            exact empty_rows_reject source result empty _ accepted
  · obtain ⟨edge, member, matched⟩ := retained
    have rows : source 1 = [row 3 [2], row 3 [3]] := rfl
    rw [rows] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have paired := matched.2.2
      change All₂ related [(2, 3)] [2] at paired
      cases paired with
      | cons head tail => exact first_separates.2 ((exactChild 2 head (.node 0 [])).mp first_separates.1).2
    · have paired := matched.2.2
      change All₂ related [(2, 3)] [3] at paired
      cases paired with
      | cons head tail => exact second_separates.2 ((exactChild 3 head (.node 2 [])).mp second_separates.1).1

end MicroCFTA.UnionDiagonalRowBoundary
