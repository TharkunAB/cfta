/-- Pre-expansion events return the complete original metadata without state reads. -/
theorem recordTypes_inr (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv node : Nat) :
    recordTypes graph templates fuel metadata uv (.inr node) = pure (false, metadata) := by
  cases templates <;> rfl
