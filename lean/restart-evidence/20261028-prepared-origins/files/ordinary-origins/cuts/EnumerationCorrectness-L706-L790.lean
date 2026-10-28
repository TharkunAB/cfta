/-- A bounded fragment depends only on the values of allocated holes. -/
theorem fill_bounded (limit : Nat) (left right : Nat → Term Symbol)
    (agree : ∀ uv < limit, left uv = right uv) (fragment : Fragment Symbol)
    (bounded : FragmentBound limit fragment) : fill left fragment = fill right fragment := by
  cases fragment with
  | hole uv => simpa [fill] using agree uv bounded
  | node symbol children =>
      simp only [fill]
      rw [fill_children_bounded limit left right agree children bounded]
termination_by sizeOf fragment

/-- Bounded child lists preserve their order and each completed subtree under agreement. -/
theorem fill_children_bounded (limit : Nat) (left right : Nat → Term Symbol)
    (agree : ∀ uv < limit, left uv = right uv) (children : List (Fragment Symbol))
    (bounded : FragmentsBound limit children) : children.map (fill left) = children.map (fill right) := by
  cases children with
  | nil => rfl
  | cons child rest =>
      have both : FragmentBound limit child ∧ FragmentsBound limit rest := bounded
      simp only [List.map_cons]
      rw [fill_bounded limit left right agree child both.1, fill_children_bounded limit left right agree rest both.2]
termination_by sizeOf children
end

/-- A bounded slot imposes the same restriction after values of fresh variables change. -/
theorem slot_assignment_congr (language : NodeLanguage Symbol) (limit uv : Nat) (allocated : uv < limit)
    (left right : Nat → Term Symbol) (agree : ∀ index < limit, left index = right index)
    (value : UVarValue Symbol) (bounded : SlotBound limit value) :
    slotSatisfies left uv (slot language value) ↔ slotSatisfies right uv (slot language value) := by
  cases value with
  | eliminated => rfl
  | enumerated fragment =>
      simp only [slot, slotSatisfies, fill_bounded limit left right agree fragment bounded, agree uv allocated]
  | unenumerated node scs =>
      simp only [slot, slotSatisfies, List.mem_map, forall_exists_index, and_imp]
      rw [agree uv allocated]
      apply and_congr Iff.rfl
      constructor
      · intro holds obligation sc member same
        subst obligation
        intro path present
        have result := holds _ sc member rfl path present
        simpa [agree sc.var (bounded sc member)] using result
      · intro holds obligation sc member same
        subst obligation
        intro path present
        have result := holds _ sc member rfl path present
        simpa [agree sc.var (bounded sc member)] using result

/-- Storage safety makes extension on fresh variables invisible to every existing state restriction. -/
theorem state_assignment_congr (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (valid : StorageValid state) (left right : Nat → Term Symbol)
    (agree : ∀ uv < state.counter, left uv = right uv) :
    Satisfies language meaning left state ↔ Satisfies language meaning right state := by
  apply and_congr
  · apply and_congr (forest_assignment_congr state.representatives state.counter valid.forest left right agree)
    apply forall_congr'
    intro uv
    cases found : state.values[uv]? with
    | none => simp [heap, found, slot, slotSatisfies]
    | some value =>
        have member := List.mem_of_getElem? found
        have inRange := (List.getElem?_eq_some_iff.mp found).1
        simpa [heap, found] using slot_assignment_congr language state.counter uv (by rw [valid.aligned]; exact inRange)
          left right agree value (valid.values value member)
  · unfold guardsHold
    apply forall_congr'
    intro obligation
    apply imp_congr_right
    intro member
    rw [fill_bounded state.counter left right agree obligation.2 (valid.guards obligation member)]

/-- Fresh class witnesses extend a valid stored assignment without losing any source equality class. -/
theorem fresh_classes_state_complete (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (valid : StorageValid state) (assignment : Nat → Term Symbol)
    (satisfies : Satisfies language meaning assignment state) (term : Term Symbol) (tries : List EqualityTrie.Trie)
    (equalities : ∀ trie ∈ tries, EqualityHolds term trie) :
    ∃ extended, Satisfies language meaning extended (suspendedState tries.length state) ∧
      (∀ uv < state.counter, extended uv = assignment uv) ∧
      ∀ sc ∈ suspendedVars state.counter tries, Suspended.Holds extended term sc := by
  obtain ⟨extended, agree, holds⟩ := (fresh_classes_exact term tries assignment state.counter).mp equalities
  have old := (state_assignment_congr language meaning state valid extended assignment agree).mpr satisfies
  exact ⟨extended, (suspendMany_semantics language meaning extended tries.length state valid.aligned).mpr old, agree, holds⟩

mutual
