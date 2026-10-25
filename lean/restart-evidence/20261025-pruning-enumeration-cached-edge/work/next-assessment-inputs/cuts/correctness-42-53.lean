theorem run_bind (action : EnumerateM Symbol Guard α) (next : α → EnumerateM Symbol Guard β)
    (state : State Symbol Guard) :
    ExceptT.run ((action >>= next) state) = (ExceptT.run (action state)).flatMap
      (fun result => match result with
        | .error error => [.error error]
        | .ok (value, after) => ExceptT.run (next value after)) := by
  simp only [bind, StateT.bind, ExceptT.run, ExceptT.bind, ExceptT.mk]
  congr 1
  funext result
  cases result with
  | error error => rfl
  | ok pair => cases pair; rfl
