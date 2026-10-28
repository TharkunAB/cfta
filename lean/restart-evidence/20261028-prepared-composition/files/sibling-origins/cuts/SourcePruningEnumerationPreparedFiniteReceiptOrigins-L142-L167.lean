  obtain ⟨fuel, outcome, resources, completedModels⟩ :=
    receipt_finite_complete_resources_models holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata formulas solver recursiveFuel original next caller reached memos final before uv receipt
      packet post advanced admitted pending history seed ceiling bounded known selectionMembers selectionLength
      mass reserved
  cases receipt with
  | unhandled => exact ⟨fuel, outcome, resources, completedModels⟩
  | rejected actual saved after => exact ⟨fuel, outcome, resources, completedModels⟩
  | stopped fragments observation candidate => exact ⟨fuel, outcome, resources, completedModels⟩
  | complete fragment actual saved afterCache =>
      obtain ⟨actualSame, savedSame, recorded, callbackCore, current, allocated, returned, equivalence, models⟩ :=
        completedModels
      refine ⟨fuel, outcome, resources, actualSame, savedSame, recorded, callbackCore,
        ⟨current, allocated, returned, equivalence, models⟩, ?_, ?_⟩
      · intro whole assignment
        rw [returned.2.2.1.counter]
      · intro language meaning assignment whole satisfied filled refuted policies origin
        have localPolicies := policies (assignment uv) origin
        have avoids : SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) := by
          simpa only [filled] using localPolicies.1
        have encoded : ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
            SourcePruningTemplates.ProgramEncoding program := by
          simpa only [filled] using localPolicies.2
        exact models language meaning assignment satisfied filled refuted avoids encoded

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
