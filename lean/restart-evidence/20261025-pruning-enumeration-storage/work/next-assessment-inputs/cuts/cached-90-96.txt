/-- State effects that keep the slots and supply keep both cached indexes correct. -/
theorem frame_correct (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (core : State Symbol Guard)
    (correct : Correct graph state) (values : core.values = state.core.values) (counter : core.counter = state.core.counter) :
    Correct graph (frame core state) := by
  refine ⟨counter.trans (correct.aligned.trans (congrArg List.length values.symm)), ?_, ?_⟩
  · intro uv; simpa [frame, values] using correct.expandable uv
  · simpa [frame, values] using correct.waiting
