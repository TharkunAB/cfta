theorem output_render_assignment
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (resources : OutputResources formulas solver original seed output)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Term Symbol → Prop) (marker : Symbol) (fuel uv : Nat)
    (after : Core) (term : Term Symbol) (pending : List (Constraint × Term Symbol))
    (discharged : SourceFlatPruningRendering.Discharged output.cache.core)
    (observed : Except.ok ((term, pending), after) ∈
      ExceptT.run (SourceFlatPruningRendering.render
        output.caller.checked.native.machine.heap marker fuel uv output.cache.core))
    (checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2) :
    ∃ assignment : Nat → Term Symbol,
      EnumerationFlatState.Satisfies
        (SourcePruningEnumerationNativeLanguage.handles holds ambient
          output.caller.checked.native.machine.heap) meaning assignment output.cache.core ∧
      term = assignment uv ∧ after = output.cache.core ∧
      EnumerationFlatState.Satisfies
        (SourcePruningEnumerationNativeLanguage.handles holds ambient
          output.caller.checked.native.machine.heap) meaning assignment after := by
