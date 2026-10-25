inductive Step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (left right : Value Symbol Guard) (before : Checked width) :
    Value Symbol Guard → Checked width → Prop where
  | run {fuel : Nat}
      (trace : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before
        (.code (.pure value)) after) : Step left right before value after

/-- A raw completed step has a literal finite checked execution. -/
theorem Step.done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {left right value : Value Symbol Guard} {before after : Checked width}
    (actual : Step left right before value after) :
    ∃ fuel, execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after := by
  cases actual with
  | run trace => exact ⟨_, trace_done _ _ before after value trace.steps⟩
