def runStaged : List (InternedConstructorTemplates.Value Symbol Constraint ×
    List EnumerationState.Suspended ×
    Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) →
    EnumerateM Symbol Constraint (Option (List (Fragments.Fragment Symbol)))
 :=
  fun stages => match stages with
  | [] => pure (some [])
  | (_, _, none) :: _ => pure none
  | (_, _, some childAction) :: rest =>
      childAction >>= fun fragment =>
        runStaged rest >>= fun result => pure (result.map (fun tail => fragment :: tail))

/-- Derive the actual completed-prefix endpoint, including the first unsupported child. -/
theorem runStaged_complete
    (inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended))
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (coherent : InternedRecordCoherence.Coherent heap) :
    ∀ (before : EnumerationState.State Symbol Constraint),
      PendingRealized heap before → before.counter = before.values.length →
      (∀ input ∈ inputs, InternedProbeProvenance.Available heap input.1) →
      (∀ input ∈ inputs, input.1.free = []) → (∀ input ∈ inputs, input.1 ≠ .empty) →
      let staged := inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1))
      let stop := staged.findIdx (fun stage => stage.2.2.isNone)
      ∃ (result : Option (List (Fragments.Fragment Symbol))) (after : EnumerationState.State Symbol Constraint),
        Success (runStaged staged) before result after ∧
        Success (runStaged (staged.take stop)) before
          (some ((List.range' before.counter stop).map (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) after ∧
        result = (if stop < staged.length then none else
          some ((List.range' before.counter staged.length).map (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) ∧
        after.counter = before.counter + stop ∧ after.counter = after.values.length ∧
        PendingRealized heap after
 := by
