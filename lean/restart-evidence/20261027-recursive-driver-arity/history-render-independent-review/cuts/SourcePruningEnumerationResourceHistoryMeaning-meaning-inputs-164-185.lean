theorem ResourceHistoryWithArity.sound
    (history : ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (canonical : Canonical before.core)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient output.caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment output.cache.core →
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core := by
  revert actualNext canonical discharged
  induction history with
  | stopped _admission =>
      intro _actualNext _canonical _discharged ambient assignment satisfied
      exact satisfied
  | done _admission =>
      intro _actualNext _canonical _discharged ambient assignment satisfied
