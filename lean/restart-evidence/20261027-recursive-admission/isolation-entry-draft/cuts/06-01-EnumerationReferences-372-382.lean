theorem incoming_read (held : Nat) (before after : State Symbol Guard) (stable : RenderStable before after)
    (incoming : IncomingAvoid held before) : IncomingAvoid held after := by
  intro value member sc listed same
  exact incoming value (by simpa [stable.values] using member) sc listed ((stable.classes held sc.var).mp same)

/-- Reads retain the avoidance of every expanded slot. -/
theorem pending_read (before after : State Symbol Guard) (stable : RenderStable before after)
    (pending : PendingReferences before) : PendingReferences after := by
  intro held fragment stored
  have original : before.values[held]? = some (.enumerated fragment) := by simpa [stable.values] using stored
  exact incoming_read held before after stable (pending held fragment original)
