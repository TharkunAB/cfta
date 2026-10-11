import MicroCFTA.ObservationGraph

/-!
# Depth-bounded graph construction

The memo key in `Interned.Operations.boundDepth` is remaining depth and node
identity. This executable graph version uses that pair as its state. Guards
and symbols stay unchanged. The finite graph theorem starts after recursive
binders have been exposed as graph references. Binder conversion is separate.
-/

namespace MicroCFTA.BoundDepth
open Language

/-- Copy one edge and decrement every child's remaining height. -/
def copyEdge (remaining : Nat) (edge : Edge State Symbol) : Edge (Nat × State) Symbol :=
  ⟨edge.label, edge.children.map (remaining, ·), edge.guard⟩

/-- Source leaf filtering at height one, with an empty graph at height zero. -/
def bound (A : Automaton State Symbol) : Automaton (Nat × State) Symbol
  | (0, _) => []
  | (remaining + 1, q) =>
      ((A q).filter (fun edge => decide (0 < remaining) || edge.children.isEmpty)).map (copyEdge remaining)

/-- Acceptance in the copied graph is exactly original acceptance below the bound. -/
theorem bound_exact (A : Automaton State Symbol) (remaining : Nat) (q : State) (t : Term Symbol) :
    Accepts (bound A) (remaining, q) t ↔ Accepts A q t ∧ t.height ≤ remaining := by
  induction remaining generalizing q t with
  | zero =>
      constructor
      · intro accepted
        cases accepted with
        | node edge children absent => simp [bound] at absent
      · rintro ⟨_, impossible⟩
        have positive := t.height_pos
        omega
  | succ remaining ih =>
      cases t with
      | node symbol ts =>
        rw [accepts_node_iff]
        constructor
        · rintro ⟨copied, present, label, children, guarded⟩
          obtain ⟨edge, filtered, same⟩ := List.mem_map.mp present
          subst copied
          have source := (List.mem_filter.mp filtered).1
          have mapped := (ObservationGraph.all₂_map_left (remaining, ·) (Accepts (bound A)) edge.children ts).mp children
          have runs := All₂.imp (fun q t h => (ih q t).mp h) mapped
          obtain ⟨runs, height⟩ := (all₂_height_iff (Accepts A) edge.children ts remaining).mp runs
          refine ⟨(accepts_node_iff A q symbol ts).mpr ⟨edge, source, label, runs, guarded⟩, ?_⟩
          simpa only [Term.height, forestHeight] using Nat.succ_le_succ height
        · rintro ⟨accepted, height⟩
          obtain ⟨edge, present, label, children, guarded⟩ := (accepts_node_iff A q symbol ts).mp accepted
          have height : forestHeight ts ≤ remaining := by
            simpa only [Term.height, forestHeight, Nat.add_le_add_iff_right] using height
          have runs := (all₂_height_iff (Accepts A) edge.children ts remaining).mpr ⟨children, height⟩
          have mapped := All₂.imp (fun q t h => (ih q t).mpr h) runs
          have kept : (decide (0 < remaining) || edge.children.isEmpty) = true := by
            by_cases positive : 0 < remaining
            · simp [positive]
            · have zero : remaining = 0 := by omega
              have tsEmpty : ts = [] := by
                cases ts with
                | nil => rfl
                | cons t rest =>
                  have low := height_le_forestHeight (t :: rest) t (by simp)
                  have high := t.height_pos
                  omega
              have qsEmpty : edge.children = [] := by
                have length := children.length_eq
                simp [tsEmpty] at length
                exact length
              simp [qsEmpty]
          exact ⟨copyEdge remaining edge,
            List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨present, kept⟩, rfl⟩,
            label, (ObservationGraph.all₂_map_left (remaining, ·) (Accepts (bound A)) edge.children ts).mpr mapped,
            guarded⟩

/-- Increasing a bound never deletes an accepted term. -/
theorem bound_monotone (A : Automaton State Symbol) (first second : Nat)
    (ordered : first ≤ second) (q : State) (t : Term Symbol)
    (accepted : Accepts (bound A) (first, q) t) : Accepts (bound A) (second, q) t := by
  obtain ⟨original, height⟩ := (bound_exact A first q t).mp accepted
  exact (bound_exact A second q t).mpr ⟨original, Nat.le_trans height ordered⟩

/-- Every finite accepted expression survives some finite depth bound. -/
theorem eventually_bounded (A : Automaton State Symbol) (q : State) (t : Term Symbol) :
    Accepts A q t ↔ ∃ remaining, Accepts (bound A) (remaining, q) t := by
  constructor
  · intro accepted
    exact ⟨t.height, (bound_exact A t.height q t).mpr ⟨accepted, Nat.le_refl _⟩⟩
  · rintro ⟨remaining, accepted⟩
    exact ((bound_exact A remaining q t).mp accepted).1

end MicroCFTA.BoundDepth
