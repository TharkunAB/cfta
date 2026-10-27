/-- Structural completion and checked rendered residuals construct a full native assignment. -/
theorem render_assignment (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : EnumGuard → Term Symbol → Prop) (marker : Symbol) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (term : Term Symbol)
    (pending : List (EnumGuard × Term Symbol)) (safe : Safe before)
    (level : Nat → Nat) (frontier : Nat) (ordered : EnumerationOrder.Stratified before level frontier)
    (discharged : Discharged before)
    (success : Success (render heap marker fuel uv) before (term, pending) after)
    (checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2) :
    ∃ assignment : Nat → Term Symbol,
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap) meaning assignment before ∧
      term = assignment uv ∧ Frame before after ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap) meaning assignment after := by
  let language := SourcePruningEnumerationNativeLanguage.handles holds ambient heap
  obtain ⟨assignment, equations⟩ := EnumerationAssignment.stratified_assignment before safe level frontier
    ordered (.node marker []) language discharged
