/-- One root keeps a native handle and has no suspended constraints or incoming suspended reference. -/
structure IsolatedPending (held handle : Nat) (state : State Symbol EnumGuard) : Prop where
  /-- The slot is a representative of its class. -/
  root : IsRoot state.representatives held
  /-- The actual pending payload retains its native handle. -/
  stored : state.values[held]? = some (.unenumerated (some handle) [])
  /-- Every stored suspended reference avoids this class. -/
  incoming : IncomingAvoid held state

/-- An isolated native pending slot contradicts full structural discharge. -/
theorem IsolatedPending.not_discharged
    (isolated : IsolatedPending held handle state) :
    ¬SourcePruningEnumerationRendering.Discharged state := by
  intro discharged
  have impossible := (discharged held (some handle) [] isolated.stored).1
  cases impossible

/-- Actual compression retains the complete isolated pending certificate. -/
theorem IsolatedPending.through_frame
    (isolated : IsolatedPending held handle before) (frame : Frame before after) :
    IsolatedPending held handle after := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨isolated.root.choose,
      (frame.reaches held held isolated.root.choose).mpr isolated.root.choose_spec⟩
  · rw [frame.values]
    exact isolated.stored
  · intro value member sc listed same
    have oldMember : value ∈ before.values := by simpa only [frame.values] using member
    exact isolated.incoming value oldMember sc listed
