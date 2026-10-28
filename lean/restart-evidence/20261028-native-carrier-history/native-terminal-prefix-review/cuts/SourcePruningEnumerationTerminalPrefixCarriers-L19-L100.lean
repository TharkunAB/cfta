/-- Actual terminal prefix success retains references and joins every recorded source. -/
theorem run_carriers (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : EnumerationState.State Symbol EnumGuard)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (observed : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after ∧
      ∀ source ∈ recorded, UnionFind.SameClass after.representatives winner source := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold run at observed
  obtain ⟨actualRecorded, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp observed
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel
    (first :: rest) before scanned actualRecorded ⟨rfl, paths⟩ scan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  let selected : List Nat := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united :=
    terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
      (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots selected
    fuel first.var actualWinner united resolved joined resolution
  obtain ⟨resultSame, afterSame⟩ := (success_pure
    (actualRecorded, actualWinner, EnumerationCanonicalWaiting.moveMany actualWinner
      (EnumerationBuilderCaches.canonicalIds (actualRecorded.filter (fun key => key != actualWinner))) waiting)
    (recorded, winner, moved) resolved after).mp final
  have recordedEq : recorded = actualRecorded := congrArg Prod.fst resultSame
  have winnerEq : winner = actualWinner := congrArg (fun result : List Nat × Nat × EnumerationWaitingIndex.Waiting => result.2.1) resultSame
  subst recorded
  subst winner
  subst after
  have scanFrame : scanned = {before with representatives := scanned.representatives} := by
    apply mapM_invariant (fun (sc : Suspended) => representative fuel sc.var)
      (fun current => current = {before with representatives := current.representatives})
      (first :: rest) ?_ before scanned actualRecorded rfl scan
    intro sc member current root next previous success
    obtain ⟨found, lookup, rootSame, nextSame⟩ :=
      (representative_success fuel sc.var current next root).mp success
    rw [nextSame]
    exact congrArg (fun state : EnumerationState.State Symbol EnumGuard =>
      {state with representatives := found.forest}) previous
  have unionFrame : united = {before with representatives := united.representatives} := by
    apply forM_invariant (fun (sc : Suspended) => unionVariables fuel first.var sc.var)
      (fun current => current = {before with representatives := current.representatives})
      rest ?_ scanned united scanFrame unions
    intro sc member current next previous success
    obtain ⟨forest, lookup, nextSame⟩ :=
      (unionVariables_success fuel first.var sc.var current next).mp success
    rw [nextSame]
    exact congrArg (fun state : EnumerationState.State Symbol EnumGuard =>
      {state with representatives := forest}) previous
  have afterFrame : resolved = {before with representatives := resolved.representatives} := by
    obtain ⟨found, lookup, rootSame, finalSame⟩ :=
      (representative_success fuel first.var united resolved actualWinner).mp resolution
    rw [finalSame]
    exact congrArg (fun state : EnumerationState.State Symbol EnumGuard =>
      {state with representatives := found.forest}) unionFrame
  have preserved : PreservesCarriers before resolved :=
    carriers_classes before resolved resolvedValid.values (fun left right same =>
      (resolvedValid.joined left right).mpr
        (Or.inl ((class_iff before.representatives roots paths left right).mp same)))
  have origin : EnumerationDependencies.EnumeratedOrigin before resolved := by
    intro uv fragment stored
    simpa only [resolvedValid.values] using stored
  have obligationsSame : resolved.obligations = before.obligations := by rw [afterFrame]
  refine ⟨resolvedValid.total, preserved,
    references_transport before resolved references preserved origin obligationsSame, ?_⟩
  have selectedMember : ∀ sc ∈ first :: rest, roots sc.var ∈ selected := by
    intro sc member
    apply (resolve_members roots rest [roots first.var] (roots sc.var)).mpr
    rcases List.mem_cons.mp member with rfl | present
    · exact Or.inl (by simp)
    · exact Or.inr ⟨sc, present, rfl⟩
  intro source member
  rw [recordedSame] at member
  obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
  have fixed : roots (roots sc.var) = roots sc.var :=
    EnumerationCanonicalUnion.roots_idempotent before.representatives roots paths sc.var
  exact UnionFind.sameClass_trans (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
    ((resolvedValid.joined first.var (roots sc.var)).mpr
      (Or.inr ⟨selectedMember first (by simp), by simpa [fixed] using selectedMember sc present⟩))
