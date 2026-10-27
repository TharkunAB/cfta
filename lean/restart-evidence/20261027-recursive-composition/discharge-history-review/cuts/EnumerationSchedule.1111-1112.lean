/-- Storage bounds and the live-representative invariant at a completed local action. -/
def Safe (state : State Symbol Guard) : Prop := StorageValid state ∧ LiveRoots state
