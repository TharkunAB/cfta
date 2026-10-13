import MicroCFTA.SourceRowsMinimumGate

/-!
# Product rows for the finite plain source region

Only pairs in the source key carrier require product-row readback.
Unrelated constrained heap nodes need no intersection contract.
The constructor contract retains the closed self-intersection shortcut,
ordered child identities, and the two checked dead-row cleanup cases.
-/
namespace MicroCFTA.SourceCyclicRowsNativeGate
open Language SymbolicGraphView

/-- The native intersection row boundary for source keys in one checked region. -/
structure ProductReadback [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (meet : Source → Source → Target) where
  diagonal : ∀ state, meet state state = encode state
  keep : Source → Source → Language.Edge (Source × Source) Symbol → Bool
  members : ∀ left right, left ≠ right → ∀ edge, edge ∈ target (meet left right) ↔
    ∃ original ∈ Language.intersect source source (left, right),
      keep left right original = true ∧ edge = renameEdge (fun pair => meet pair.1 pair.2) original
  rejected : ∀ left right, left ≠ right → ∀ edge,
    edge ∈ Language.intersect source source (left, right) → keep left right edge = false →
      DropReason target (fun pair => meet pair.1 pair.2) edge

/-- Local copied product rows derive complete intersection, including diagonal reuse. -/
theorem product_exact [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (copied : RowsCorrespond source target encode)
    (meet : Source → Source → Target) (view : ProductReadback source target encode meet)
    (left right : Source) (term : Term Symbol) :
    Accepts target (meet left right) term ↔ Accepts source left term ∧ Accepts source right term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ left right,
      Accepts target (meet left right) term ↔ Accepts source left term ∧ Accepts source right term)
    generalizing left right with
  | node symbol children ih =>
    by_cases same : left = right
    · subst right
      rw [view.diagonal, rowsCorrespond_exact source target encode copied]
      exact ⟨fun accepted => ⟨accepted, accepted⟩, And.left⟩
    · rw [← accepts_intersect_iff source source left right, accepts_node_iff, accepts_node_iff]
      have childExact : ∀ tree ∈ children, ∀ pair : Source × Source,
          Accepts target (meet pair.1 pair.2) tree ↔
            Accepts (Language.intersect source source) pair tree := by
        intro tree member pair
        rw [accepts_intersect_iff]
        exact ih tree member pair.1 pair.2
      constructor
      · rintro ⟨edge, member, label, runs, guard⟩
        obtain ⟨original, present, _, rfl⟩ := (view.members left right same edge).mp member
        have mapped := (all₂_map_iff (Accepts target) (fun pair : Source × Source => meet pair.1 pair.2)
          original.children children).mp runs
        exact ⟨original, present, label, GraphRewrite.all₂_local_imp _ _ mapped
          (fun pair tree member => (childExact tree member pair).mp), guard⟩
      · rintro ⟨edge, member, label, runs, guard⟩
        have copiedRuns : All₂ (fun pair tree => Accepts target (meet pair.1 pair.2) tree) edge.children children :=
          GraphRewrite.all₂_local_imp _ _ runs (fun pair tree member => (childExact tree member pair).mpr)
        have retained : view.keep left right edge = true := by
          cases choice : view.keep left right edge with
          | true => rfl
          | false =>
            rcases view.rejected left right same edge member choice with impossibleGuard | ⟨child, present, empty⟩
            · have impossible := impossibleGuard (.node symbol children)
              simp [guard] at impossible
            · obtain ⟨subtree, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ copiedRuns child present
              exact False.elim (empty_rows_reject target (meet child.1 child.2) empty subtree accepted)
        refine ⟨renameEdge (fun pair => meet pair.1 pair.2) edge,
          (view.members left right same _).mpr ⟨edge, member, retained, rfl⟩, label, ?_, guard⟩
        exact (all₂_map_iff (Accepts target) (fun pair : Source × Source => meet pair.1 pair.2)
          edge.children children).mpr copiedRuns
  | nil => simp_all
  | cons first rest head tail =>
    rename_i term member left right
    rcases List.mem_cons.mp member with rfl | member
    · exact head left right
    · exact tail term member left right

/-- The original global product interface implies the scoped row interface. -/
def ofProductRows [DecidableEq State] [DecidableEq Symbol]
    (graph : Automaton State Symbol) (meet : State → State → State)
    (product : ProductRows graph meet) : ProductReadback graph graph id meet where
  diagonal := product.diagonal
  keep := product.keep
  members := product.members
  rejected := product.rejected

end MicroCFTA.SourceCyclicRowsNativeGate
