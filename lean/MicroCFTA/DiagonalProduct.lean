import MicroCFTA.RelatedRows

/-!
# Synchronous product rows with diagonal reuse

A diagonal state copies its source rows with diagonal child pairs. Other
states retain the ordinary synchronous product. This follows the closed
self shortcut without requiring one physical representative for each pair.
The complete finite-term language is the source intersection.
-/
namespace MicroCFTA.DiagonalProduct
open Language SymbolicGraphView

/-- Copy diagonal rows and retain complete synchronous rows at every other pair. -/
def graph [DecidableEq State] [DecidableEq Symbol] (source : Automaton State Symbol) : Automaton (State × State) Symbol :=
  fun pair => if pair.1 = pair.2 then (source pair.1).map (renameEdge (fun state => (state, state)))
    else Language.intersect source source pair

/-- A diagonal product state has precisely the copied original rows. -/
theorem diagonal_rows [DecidableEq State] [DecidableEq Symbol] (source : Automaton State Symbol) (state : State) :
    graph source (state, state) = (source state).map (renameEdge (fun child => (child, child))) := by
  simp [graph]

/-- Diagonal reuse preserves the complete synchronous product language, including ambiguous source rows. -/
theorem language_exact [DecidableEq State] [DecidableEq Symbol] (source : Automaton State Symbol)
    (first second : State) (term : Term Symbol) :
    Accepts (graph source) (first, second) term ↔ Accepts source first term ∧ Accepts source second term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ first second,
      Accepts (graph source) (first, second) term ↔ Accepts source first term ∧ Accepts source second term)
    generalizing first second with
  | node symbol children ih =>
      by_cases same : first = second
      · subst second
        rw [and_self, accepts_node_iff, diagonal_rows, accepts_node_iff]
        constructor
        · rintro ⟨edge, member, label, runs, guard⟩
          obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
          have paired := (all₂_map_iff _ (fun state => (state, state)) original.children children).mp runs
          refine ⟨original, present, label, ?_, guard⟩
          exact GraphRewrite.all₂_local_imp _ _ paired (fun state tree member accepted => ((ih tree member state state).mp accepted).1)
        · rintro ⟨original, present, label, runs, guard⟩
          refine ⟨renameEdge (fun state => (state, state)) original, List.mem_map.mpr ⟨original, present, rfl⟩, label, ?_, guard⟩
          apply (all₂_map_iff _ (fun state => (state, state)) original.children children).mpr
          exact GraphRewrite.all₂_local_imp _ _ runs (fun state tree member accepted => (ih tree member state state).mpr ⟨accepted, accepted⟩)
      · rw [← accepts_intersect_iff source source first second, accepts_node_iff, accepts_node_iff]
        simp only [graph, ite_eq_right same]
        constructor
        · rintro ⟨edge, member, label, runs, guard⟩
          refine ⟨edge, member, label, ?_, guard⟩
          exact GraphRewrite.all₂_local_imp _ _ runs (fun pair tree member accepted =>
            (accepts_intersect_iff source source pair.1 pair.2 tree).mpr ((ih tree member pair.1 pair.2).mp accepted))
        · rintro ⟨edge, member, label, runs, guard⟩
          refine ⟨edge, member, label, ?_, guard⟩
          exact GraphRewrite.all₂_local_imp _ _ runs (fun pair tree member accepted =>
            (ih tree member pair.1 pair.2).mpr ((accepts_intersect_iff source source pair.1 pair.2 tree).mp accepted))
  | nil => simp_all
  | cons head tail first rest =>
      rename_i term member left right
      rcases List.mem_cons.mp member with rfl | member
      · exact first left right
      · exact rest term member left right

/-- Related physical rows of this product derive complete two-input language without a functional child map. -/
theorem related_product_exact [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (related : (Source × Source) → Target → Prop) (view : RelatedRows.Readback (graph source) target related)
    (first second : Source) (result : Target) (paired : related (first, second) result) (term : Term Symbol) :
    Accepts target result term ↔ Accepts source first term ∧ Accepts source second term :=
  (RelatedRows.language_exact (graph source) target related view (first, second) result paired term).trans
    (language_exact source first second term)

end MicroCFTA.DiagonalProduct
