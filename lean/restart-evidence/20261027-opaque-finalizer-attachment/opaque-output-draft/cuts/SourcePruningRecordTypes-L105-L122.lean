/-- Every successful callback preserves all modeled compression fields and root paths. -/
theorem recordTypes_frame (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (before after : State Symbol Guard) (result : Bool × Metadata Typing)
    (total : UnionFind.Total before.representatives)
    (success : Success (recordTypes graph templates fuel metadata uv input) before result after) :
    Frame before after := by
  cases templates with
  | nil =>
      rw [recordTypes_empty] at success
      exact pure_frame _ result before after success
  | cons first rest =>
      change Success (SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv input >>= fun observed =>
        pure (observed.1, {metadata with pending := observed.2, types := updatedTypes metadata uv input}))
        before result after at success
      obtain ⟨observed, middle, read, finished⟩ := (success_bind _ _ _ _ _).mp success
      exact (SourcePruningOracle.oracle_frame graph (first :: rest) fuel metadata.pending uv input
        before middle observed total read).trans (pure_frame _ result middle after finished)
