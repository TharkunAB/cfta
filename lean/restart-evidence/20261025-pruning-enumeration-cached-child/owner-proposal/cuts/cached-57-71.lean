theorem allocate_correct (graph : Graph Symbol Guard) (node : Option Nat) (state : Cached Symbol Guard)
    (correct : Correct graph state) : Correct graph (allocate graph node state) := by
  refine ⟨allocated_supply node state.core correct.aligned, ?_, EnumerationWaitingIndex.allocate_correct _ node _ correct.waiting⟩
  intro uv
  by_cases before : uv < state.core.values.length
  · have different : uv ≠ state.core.counter := by rw [correct.aligned]; omega
    simp only [allocate, allocated, List.getElem?_append_left before]
    simp [different, correct.expandable uv]
  · by_cases same : uv = state.core.counter
    · simp [allocate, allocated, correct.aligned, same, correct.expandable]
    · have after : state.core.values.length < uv := by rw [correct.aligned] at same; omega
      have absent : state.core.values[uv]? = none := List.getElem?_eq_none (by omega)
      have wholeAbsent : (state.core.values ++ [.unenumerated node []])[uv]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp [allocate, allocated, same, wholeAbsent, correct.expandable, absent]
