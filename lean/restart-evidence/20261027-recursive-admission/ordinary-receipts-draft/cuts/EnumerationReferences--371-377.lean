/-- A value-preserving class-preserving read retains a protected root's incoming-reference condition. -/
theorem incoming_read (held : Nat) (before after : State Symbol Guard) (stable : RenderStable before after)
    (incoming : IncomingAvoid held before) : IncomingAvoid held after := by
  intro value member sc listed same
  exact incoming value (by simpa [stable.values] using member) sc listed ((stable.classes held sc.var).mp same)

/-- Reads retain the avoidance of every expanded slot. -/
