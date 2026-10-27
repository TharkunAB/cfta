theorem recordTypes_replays (graph : EnumerationState.Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat) (metadata : Metadata Typing)
    (uv : Nat) (input : Sum (Fragment Symbol) Nat) :
    Replays (recordTypes graph templates fuel metadata uv input)
      (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input) := by
  dsimp only [recordTypes, SourcePruningRecordTypes.recordTypes]
  by_cases empty : templates.isEmpty
  · simp only [empty, ↓reduceIte]
    exact bind_replays _ _ _ _ (pure_replays (false, metadata.pending)) (fun _ => pure_replays _)
  · simp only [empty]
    exact bind_replays _ _ _ _ (oracle_replays graph templates fuel metadata.pending uv input)
      (fun _ => pure_replays _)

end MicroCFTA.SourceFlatPruningOracle
