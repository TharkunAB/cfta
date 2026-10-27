theorem render_assignment (native : InternedConstructorTemplates.State Symbol NativeGuard)
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : EnumGuard → Term Symbol → Prop) (marker : Symbol) (fuel uv : Nat)
    (before after : State Symbol EnumGuard) (earlier : EnumerationState.State Symbol EnumGuard)
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
