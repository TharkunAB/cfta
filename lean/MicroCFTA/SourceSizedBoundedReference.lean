import MicroCFTA.SourceSizedApiLaws

/-!
# Bounded classes as one exact reference sequence

A complete-term size guard retains the original row order. Its reference
classes equal the original classes through the signed bound and are empty
after it. This graph certifies bounded queries; it does not replace the
actual bounded source worker.
-/
namespace MicroCFTA.SourceSizedBoundedReference
open Language RecursiveSize SourceSizedCandidates SourceSizedReference

/-- Add the signed size bound to one complete-term guard. -/
def edge (bound : Int) (row : Edge State Symbol) : Edge State Symbol :=
  { row with guard := fun term => row.guard term && decide ((nodeSize term : Int) ≤ bound) }

/-- Retain every original row and add the same complete-term size check. -/
def rows (A : Automaton State Symbol) (bound : Int) : Automaton State Symbol :=
  fun state => (A state).map (edge bound)

/-- Every candidate built from reference child classes has the requested node count. -/
theorem candidate_size [DecidableEq Symbol] (A : Automaton State Symbol) (row : Edge State Symbol)
    (size : Nat) (term : Term Symbol)
    (member : term ∈ candidates (fun state size => classes A size state) row.label row.children size) :
    nodeSize term = size := by
  cases size with
  | zero => cases member
  | succ remaining =>
      obtain ⟨_, _, _, sized⟩ := (mem_candidates_succ_iff (Accepts A) (fun state size => classes A size state) remaining
        (fun size _ state term => mem_classes_iff A size state term) row.label row.children remaining
        (Nat.le_refl _) term).mp member
      exact sized

/-- The extra guard filters a complete candidate class by its one requested size. -/
theorem filter_edge [DecidableEq Symbol] (A : Automaton State Symbol) (row : Edge State Symbol)
    (bound : Int) (size : Nat) :
    (candidates (fun state size => classes A size state) row.label row.children size).filter (edge bound row).guard =
      if (size : Int) ≤ bound then
        (candidates (fun state size => classes A size state) row.label row.children size).filter row.guard else [] := by
  by_cases within : (size : Int) ≤ bound
  · rw [ite_eq_left within]
    apply List.filter_congr
    intro term member
    simp [edge, candidate_size A row size term member, within]
  · rw [ite_eq_right within]
    apply List.filter_eq_nil_iff.mpr
    intro term member
    simp [edge, candidate_size A row size term member, within]

/-- A bounded row class uses the original first-occurrence order or is empty. -/
theorem classOf_rows [DecidableEq Symbol] (A : Automaton State Symbol) (original : List (Edge State Symbol))
    (bound : Int) (size : Nat) :
    classOf (fun state size => classes A size state) (original.map (edge bound)) size =
      if (size : Int) ≤ bound then classOf (fun state size => classes A size state) original size else [] := by
  simp only [classOf, List.flatMap_map]
  have filtered (row : Edge State Symbol) :
      (candidates (fun state size => classes A size state) (edge bound row).label (edge bound row).children size).filter
        (edge bound row).guard =
        if (size : Int) ≤ bound then
          (candidates (fun state size => classes A size state) row.label row.children size).filter row.guard else [] :=
    filter_edge A row bound size
  simp only [filtered]
  by_cases within : (size : Int) ≤ bound
  · simp only [ite_eq_left within]
  · simp only [ite_eq_right within]
    have empty : original.flatMap (fun _ => ([] : List (Term Symbol))) = [] :=
      List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
    rw [empty]
    rfl

/-- Every bounded reference class equals the original ordered class through the bound. -/
theorem classes_eq [DecidableEq Symbol] (A : Automaton State Symbol) (bound : Int) (size : Nat) (state : State) :
    classes (rows A bound) size state = if (size : Int) ≤ bound then classes A size state else [] := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => simp [classes_zero]
      | succ remaining =>
          rw [classes_succ]
          change classOf (fun child size => classes (rows A bound) size child)
            ((A state).map (edge bound)) (remaining + 1) = _
          rw [classOf_rows]
          by_cases within : ((remaining + 1 : Nat) : Int) ≤ bound
          · rw [ite_eq_left within, ite_eq_left within, classes_succ]
            apply classOf_congr
            intro child childSize smaller
            rw [ih childSize smaller child, ite_eq_left (show (childSize : Int) ≤ bound by omega)]
          · rw [ite_eq_right within, ite_eq_right within]

/-- The certificate graph accepts exactly the original terms within the signed bound. -/
theorem accepts_iff [DecidableEq Symbol] (A : Automaton State Symbol) (bound : Int) (state : State) (term : Term Symbol) :
    Accepts (rows A bound) state term ↔ Accepts A state term ∧ (nodeSize term : Int) ≤ bound := by
  have member := mem_classes_iff (rows A bound) (nodeSize term) state term
  have original := mem_classes_iff A (nodeSize term) state term
  rw [classes_eq] at member
  by_cases within : (nodeSize term : Int) ≤ bound <;> simp_all

end MicroCFTA.SourceSizedBoundedReference
