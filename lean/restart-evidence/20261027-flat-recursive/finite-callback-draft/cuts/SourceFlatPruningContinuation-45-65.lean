theorem continueWith_exact
    (callbackFailure : Nat → List (Except Error ((Bool × Metadata Typing) × Core)) → Failure)
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (fragment : Fragments.Fragment Symbol) (caller : Caller width) (queries : Queries)
    (before : Cached) (result : Bool × Metadata Typing) (after : Core)
    (observed : SourceFlatPruningOracle.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment) before.core = [.ok (result, after)]) :
    continueWith callbackFailure recur graph templates stop order callbackFuel metadata uv fragment caller queries before =
      if result.1 then .complete [] caller queries
      else recur result.2 caller queries (EnumerationFlatCached.frame after before)
        (SourceFlatPruningRestart.decision stop order result.2 (EnumerationFlatCached.frame after before)) := by
  unfold continueWith
  rw [observed]
  rcases result with ⟨pruned, updated⟩
  cases pruned <;> rfl

end MicroCFTA.SourceFlatPruningContinuation
