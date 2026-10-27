/-- Source slot writes update one in-range heap entry and no other entry. -/
theorem heap_set (language : NodeLanguage Symbol) (values : List (UVarValue Symbol))
    (uv : Nat) (value : UVarValue Symbol) (bound : uv < values.length) :
    heap language (values.set uv value) = Fragments.setSlot (heap language values) uv (slot language value) := by
  funext other
  by_cases same : other = uv
  · subst other
    simp [heap, Fragments.setSlot, bound]
  · simp [heap, Fragments.setSlot, same, Ne.symm same]
