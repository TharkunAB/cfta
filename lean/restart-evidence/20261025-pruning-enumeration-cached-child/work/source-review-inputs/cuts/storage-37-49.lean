def Success (action : EnumerateM Symbol Guard α) (before : State Symbol Guard)
    (value : α) (after : State Symbol Guard) : Prop :=
  Except.ok (value, after) ∈ ExceptT.run (action before)

/-- Binding runs each successful branch in its own stored state and retains error branches. -/
theorem run_bind (action : EnumerateM Symbol Guard α) (next : α → EnumerateM Symbol Guard β)
    (state : State Symbol Guard) :
    ExceptT.run ((action >>= next) state) = (ExceptT.run (action state)).flatMap
      (fun result => match result with
        | .error error => [.error error]
        | .ok (value, after) => ExceptT.run (next value after)) := by
  simp only [bind, StateT.bind, ExceptT.run, ExceptT.bind, ExceptT.mk]
  congr 1
