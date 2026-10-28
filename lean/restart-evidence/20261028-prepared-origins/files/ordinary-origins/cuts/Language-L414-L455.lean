
/-- A child height does not exceed the greatest height in its child list. -/
theorem height_le_forestHeight {Symbol : Type} (ts : List (Term Symbol))
    (t : Term Symbol) (h : t ∈ ts) : t.height ≤ forestHeight ts := by
  induction ts with
  | nil => simp at h
  | cons u us ih =>
      rcases List.mem_cons.mp h with heq | htail
      · subst t
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/-- Each path step strictly decreases the available tree height. -/
theorem atPath_height_bound {Symbol : Type} (t u : Term Symbol) (p : List Nat)
    (h : t.atPath p = some u) : u.height + p.length ≤ t.height := by
  induction p generalizing t with
  | nil =>
      have heq : t = u := Option.some.inj h
      subst t
      simp
  | cons i rest ih =>
      cases t with
      | node symbol ts =>
          obtain ⟨child, hchild, hu⟩ := Option.bind_eq_some_iff.mp h
          have hrec := ih child hu
          have hbound := height_le_forestHeight ts child (List.mem_of_getElem? hchild)
          simp only [Term.height, List.length_cons]
          change u.height + (rest.length + 1) ≤ forestHeight ts + 1
          omega

/-- Following a concatenated path equals following its two parts in order. -/
theorem atPath_append {Symbol : Type} (t : Term Symbol) (p rest : List Nat) :
    t.atPath (p ++ rest) = (t.atPath p).bind (fun u => u.atPath rest) := by
  induction p generalizing t with
  | nil => simp [Term.atPath]
  | cons i p ih =>
      cases t with
      | node symbol ts =>
          simp only [List.cons_append, Term.atPath]
          cases hchild : ts[i]? with
          | none => rfl
          | some child => simpa using ih child
