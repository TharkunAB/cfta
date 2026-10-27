attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- Every actual successful terminal prefix retains canonical stored suspended tries. -/
theorem run_canonical
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State SourcePruningTemplates.Symbol EnumGuard)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (canonical : Canonical before)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    Canonical after := by
  unfold run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedCanonical := mapM_invariant (fun sc => representative fuel sc.var) Canonical (first :: rest)
    (fun sc _ previous result next valid step => representative_canonical fuel sc.var result previous next valid step)
    before scanned actualRecorded canonical scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedCanonical := forM_invariant (fun sc => unionVariables fuel first.var sc.var) Canonical rest
    (fun sc _ previous next valid step => unionVariables_canonical fuel first.var sc.var previous next valid step)
    scanned united scannedCanonical unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedCanonical := representative_canonical fuel first.var actualWinner united resolved
    unitedCanonical resolution
  obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
  exact resolvedCanonical
