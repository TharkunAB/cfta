  | .inr _ => metadata.types

/-- The actual callback updates only the pending checks and type-position set. -/
def recordTypes (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) : Oracle Symbol Guard (Metadata Typing) := fun metadata uv input => do
  let types := updatedTypes metadata uv input
  let observed ← if templates.isEmpty then pure (false, metadata.pending)
    else SourcePruningOracle.oracle graph templates fuel metadata.pending uv input
  pure (observed.1, {metadata with pending := observed.2, types := types})

/-- A pending candidate has priority over type-position membership. -/
