
/-- Other source effects update the original state without changing either index. -/
def frame (core : State Symbol Guard) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  {state with core := core}
