      (EnumerationPureSelection.transfer target sources (EnumerationExpandableIndex.frame after state)) ∧
    Roots after.representatives (mergedRoots roots ((first :: rest).map (fun sc => roots sc.var)) target) := by
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined := terminal_unions state.core.values roots [roots first.var] fuel first.var rest state.core united
    (merging_initial state.core.values roots state.core first.var ⟨rfl, paths⟩) (by simp) unions
  obtain ⟨resolved, count, path⟩ := merging_representative state.core.values roots selected fuel first.var target
    united after joined winner
  have firstSelected : roots first.var ∈ selected :=
    (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
  have actualRoots := merging_roots state.core.values roots selected after resolved first.var target count firstSelected path
  have selectedSame (key : Nat) : key ∈ selected ↔ key ∈ (first :: rest).map (fun sc => roots sc.var) := by
    simp [selected, or_comm]
  have counterUnited : united.counter = state.core.counter := by
    apply forM_invariant (fun sc => unionVariables fuel first.var sc.var)
      (fun current => current.counter = state.core.counter) rest _ state.core united rfl unions
    intro sc _ before next previous success
    obtain ⟨forest, _, same⟩ := (unionVariables_success fuel first.var sc.var before next).mp success
    rw [same]
    exact previous
  obtain ⟨found, _, _, finalSame⟩ := (representative_success fuel first.var united after target).mp winner
  have counterAfter : after.counter = state.core.counter := by
    rw [finalSame]
    exact counterUnited
  have framed := EnumerationPureSelection.frame_correct graph roots state after correct resolved.values counterAfter
  have transferred := EnumerationPureSelection.transfer_correct graph roots target sources
    (EnumerationExpandableIndex.frame after state) framed
  rw [redirect_fold_eq roots ((first :: rest).map (fun sc => roots sc.var)) target sources keys] at transferred
  refine ⟨transferred, ?_⟩
  intro uv
  simpa only [mergedRoots, selectedSame] using actualRoots uv

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

end MicroCFTA.EnumerationCanonicalUnion
