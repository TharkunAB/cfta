def PrefixMeaning
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel uv : Nat) (caller : Caller width) (before : OldCached) (flat : FlatCached)
    (observed : Result width Typing) : Prop :=
  match observed with
  | .stopped _ _ | .parked _ none _ => False
  | .parked _ (some after) _ =>
      ∃ (oldHandle : Nat) (scs : List Suspended)
        (readAfter : EnumerationState.State Symbol Constraint),
        before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
        ExceptT.run (getValue fuel uv before.core) =
          [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
        ∀ ambient residualMeaning assignment,
          EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment flat.core ↔
          EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment after.core ∧
          ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc
  | .narrowed _ _ reached _ _ (some after) _ =>
      ∀ ambient residualMeaning assignment,
        EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap)
          residualMeaning assignment after.core →
        EnumerationFlatState.Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          residualMeaning assignment flat.core
