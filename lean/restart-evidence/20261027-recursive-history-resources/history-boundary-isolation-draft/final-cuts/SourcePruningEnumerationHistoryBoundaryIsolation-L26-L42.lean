private theorem restart_row_fields
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata updated : Metadata Typing)
    (before : Cached) (checked core : Core) (next : Option Next)
    (observed : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata before checked) =
      [.ok ((updated, next), core)]) :
    updated = metadata ∧ next = SourcePruningEnumerationRestart.decision stop order metadata before ∧
      core = checked := by
  change (if SourcePruningEnumerationRestart.decision stop order metadata before = some .stuck then []
    else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata before), checked)]) =
      [Except.ok ((updated, next), core)] at observed
  split at observed
  · cases observed
  · have same : metadata = updated ∧
        SourcePruningEnumerationRestart.decision stop order metadata before = next ∧ checked = core := by
      simpa only [List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, and_true, and_assoc] using observed
    exact ⟨same.1.symm, same.2.1.symm, same.2.2.symm⟩
