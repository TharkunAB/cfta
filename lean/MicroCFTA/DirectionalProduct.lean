import MicroCFTA.DirectionalRows
import MicroCFTA.DiagonalProduct

/-!
# Directional product rows include projection and retained copies

Projection covers redundant product rows by an original operand row.
The reverse copy proof uses literal row inclusion at one original root.
Both proofs retain complete guards and ordered children. They do not assume
a product-language theorem or exact child representatives.
-/
namespace MicroCFTA.DirectionalProduct
open Language SymbolicGraphView DirectionalRows

/-- Equal-length zipped source children project to the original right child list. -/
theorem zip_right (left right : List State) (length : left.length = right.length) :
    All₂ (fun pair state => pair.2 = state) (left.zip right) right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all; exact .nil
  | cons first rest ih =>
      cases right with
      | nil => simp at length
      | cons other later => exact .cons rfl (ih later (Nat.succ.inj length))

/-- Copied diagonal children project to the same original ordered children. -/
theorem diagonal_right (children : List State) :
    All₂ (fun pair state => pair.2 = state) (children.map (fun state => (state, state))) children := by
  induction children with
  | nil => exact .nil
  | cons first rest ih => exact .cons rfl ih

/-- Every diagonal or ordinary product row is covered by its original right operand row. -/
theorem project_right [DecidableEq State] [DecidableEq Symbol] (source : Automaton State Symbol) :
    Simulation (DiagonalProduct.graph source) source (fun pair state => pair.2 = state) := by
  constructor
  rintro ⟨first, second⟩ result rfl original member
  by_cases same : first = second
  · subst second
    rw [DiagonalProduct.diagonal_rows] at member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
    exact Or.inr (Or.inr ⟨edge, present, rfl, fun _ accepted => accepted, diagonal_right edge.children⟩)
  · have productMember : original ∈ Language.intersect source source (first, second) := by
      simpa only [DiagonalProduct.graph, ite_eq_right same] using member
    obtain ⟨left, _, right, present, symbol, length, rfl⟩ := (mem_intersect_iff source source first second original).mp productMember
    exact Or.inr (Or.inr ⟨right, present, symbol,
      (fun _ accepted => (Bool.and_eq_true_iff.mp accepted).2), zip_right left.children right.children length⟩)

/-- A copied source row has a product row at any roots that both contain that complete source row. -/
theorem copied_row_member [DecidableEq State] [DecidableEq Symbol] (source : Automaton State Symbol)
    (first second : State) (edge : Edge State Symbol) (left : edge ∈ source first) (right : edge ∈ source second) :
    renameEdge (fun state => (state, state)) edge ∈ DiagonalProduct.graph source (first, second) := by
  by_cases same : first = second
  · subst second
    rw [DiagonalProduct.diagonal_rows]
    exact List.mem_map.mpr ⟨edge, left, rfl⟩
  · change _ ∈ (if first = second then _ else Language.intersect source source (first, second))
    rw [ite_eq_right same]
    apply (mem_intersect_iff source source first second _).mpr
    refine ⟨edge, left, edge, right, rfl, rfl, ?_⟩
    have zipped : edge.children.zip edge.children = edge.children.map (fun state => (state, state)) := by
      induction edge.children with
      | nil => rfl
      | cons first rest ih => simp only [List.zip_cons_cons, List.map_cons, ih]
    simp only [renameEdge, zipped]
    congr 1
    funext term
    exact (Bool.and_self _).symm

/-- Literal root-row inclusion supplies a reverse simulation through diagonal child copies. -/
theorem copy_into_right [DecidableEq State] [DecidableEq Symbol] (source : Automaton State Symbol)
    (first second : State) (rows : ∀ edge ∈ source second, edge ∈ source first) :
    Simulation source (DiagonalProduct.graph source) (fun state pair =>
      pair = (state, state) ∨ state = second ∧ pair = (first, second)) := by
  constructor
  intro state pair paired edge member
  have children := (RelatedRows.rename_match (fun state => (state, state)) edge).2.2
  have covered : All₂ (fun state pair => pair = (state, state) ∨ state = second ∧ pair = (first, second))
      edge.children ((renameEdge (fun state => (state, state)) edge).children) :=
    children.imp (fun _ _ same => Or.inl same)
  refine Or.inr (Or.inr ⟨renameEdge (fun state => (state, state)) edge, ?_, rfl, fun _ accepted => accepted, covered⟩)
  rcases paired with rfl | ⟨same, rfl⟩
  · exact copied_row_member source state state edge member member
  · subst state
    exact copied_row_member source first second edge (rows edge member) member

end MicroCFTA.DirectionalProduct
