    (term : Term Symbol) (pending : List (EnumGuard × Term Symbol))
    (related : Related before earlier) (safe : EnumerationSchedule.Safe earlier)
    (level : Nat → Nat) (frontier : Nat) (ordered : EnumerationOrder.Stratified earlier level frontier)
    (discharged : Discharged before)
    (observed : Except.ok ((term, pending), after) ∈ ExceptT.run (render native marker fuel uv before))
    (checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2) :
    ∃ assignment : Nat → Term Symbol,
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient native) meaning assignment before ∧
      term = assignment uv ∧ after = before ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient native) meaning assignment after := by
  let language := SourcePruningEnumerationNativeLanguage.handles holds ambient native
  have oldDischarged : SourcePruningEnumerationRendering.Discharged earlier := by
    intro held node scs stored
    exact discharged held node scs (by simpa only [related.values] using stored)
  obtain ⟨assignment, equations⟩ := EnumerationAssignment.stratified_assignment earlier safe
    level frontier ordered (.node marker []) language oldDischarged
  have flatEquations := (related_satisfies related language (fun _ _ => True) assignment).mp
    ⟨equations, by simp [guardsHold]⟩
  have valid : Valid language assignment before := ⟨related.valid, flatEquations.1, discharged⟩
