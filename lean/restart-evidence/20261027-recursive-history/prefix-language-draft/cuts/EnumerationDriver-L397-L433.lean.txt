structure Ready (uv : Nat) (state : State Symbol Guard) : Prop where
  safe : Safe state
  inside : uv < state.counter
  root : IsRoot state.representatives uv
  avoids : ∀ node scs, state.values[uv]? = some (.unenumerated (some node) scs) →
    Avoids state.representatives uv scs

/-- Scheduler selection establishes the precondition for the caller's final write. -/
theorem findExpandable_ready (graph : Graph Symbol Guard) (fuel uv : Nat) (before after : State Symbol Guard)
    (available : Option (List Nat)) (preference : List Nat → Option Nat) (safe : Safe before)
    (success : Success (findExpandable graph fuel) before available after)
    (selected : pickNext preference available = .expand uv) : Ready uv after := by
  cases available with
  | none => cases selected
  | some available =>
      have member := pickNext_safe preference available uv selected
      obtain ⟨_, root, ⟨value, stored, _⟩, avoids⟩ := findExpandable_safe graph fuel before after available uv
        safe.1.total safe.2 success member
      have safeAfter := (findExpandable_safety graph fuel before after (some available) safe success).1
      refine ⟨safeAfter, ?_, root, fun node scs stored => avoids uv (some node) scs stored⟩
      have bound := (List.getElem?_eq_some_iff.mp stored).1
      rw [safeAfter.1.aligned]
      exact bound

/-- A root read retains the caller's ready-to-expand condition. -/
theorem getValue_ready (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (ready : Ready uv before) (success : Success (getValue fuel uv) before value after) :
    Ready uv after ∧ after.counter = before.counter := by
  obtain ⟨safeAfter, counter, frame, _⟩ := getValue_root fuel uv before after value ready.safe ready.inside ready.root success
  refine ⟨⟨safeAfter, by simpa [counter] using ready.inside, frame.root, ?_⟩, counter⟩
  intro node scs stored
  exact frame.avoids scs (ready.avoids node scs (frame.value ▸ stored))

/-- The source repeated-recursion branch clears only the selected pending constraints. -/
def checkRepeated (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended) :
    EnumerateM Symbol Guard Bool := do
  match graph.node node with
