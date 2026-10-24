/-- The actual recorded prefix and union run give one completed cached endpoint. -/
theorem recorded_transfer_correct (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (state : Cached Symbol Guard) (correct : EnumerationPureSelection.Correct graph roots state)
    (paths : Roots state.core.representatives roots) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (recorded : List Nat) (scanned united after : State Symbol Guard) (target : Nat) (sources : List Nat)
    (preScan : Success ((first :: rest).mapM fun sc => representative fuel sc.var) state.core recorded scanned)
    (unions : Success (rest.forM fun sc => unionVariables fuel first.var sc.var) scanned () united)
    (winner : Success (representative fuel first.var) united target after)
    (keys : ∀ key, key ∈ sources ↔ key ∈ recorded ∧ key ≠ target) :
    EnumerationPureSelection.Correct graph (mergedRoots roots recorded target)
      (EnumerationPureSelection.transfer target sources (EnumerationExpandableIndex.frame after state)) ∧
    Roots after.representatives (mergedRoots roots recorded target) := by
  obtain ⟨scanValid, recordedEq⟩ := representatives_scan state.core.values roots fuel (first :: rest)
    state.core scanned recorded ⟨rfl, paths⟩ preScan
  have counterScan : scanned.counter = state.core.counter := by
    apply mapM_invariant (fun sc => representative fuel sc.var)
      (fun current => current.counter = state.core.counter) (first :: rest)
      _ state.core scanned recorded rfl preScan
    intro sc _ before root next previous success
    obtain ⟨found, _, _, same⟩ := (representative_success fuel sc.var before next root).mp success
    rw [same]
    exact previous
  have scannedCorrect := EnumerationPureSelection.frame_correct graph roots state scanned correct
    scanValid.values counterScan
  have actualKeys (key : Nat) :
      key ∈ sources ↔ key ∈ (first :: rest).map (fun sc => roots sc.var) ∧ key ≠ target := by
    simpa only [recordedEq] using keys key
  have transferred := terminal_transfer_correct graph roots (EnumerationExpandableIndex.frame scanned state)
    scannedCorrect scanValid.roots fuel first rest united after target sources unions winner actualKeys
  simpa only [recordedEq, EnumerationExpandableIndex.frame] using transferred
