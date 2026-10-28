  have joined : Merging before.values roots selected united := by
    exact terminal_unions before.values roots [roots first.var] unionFuel first.var rest
      scanned united (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨rootFuel, winner, after, resolution, afterTotal⟩ := representative_terminates united unionTotal first.var
  obtain ⟨resolved, count, winnerPath⟩ := merging_representative before.values roots selected
    rootFuel first.var winner united after joined resolution
  have scanFrame : scanned = {before with representatives := scanned.representatives} := by
    apply mapM_invariant (fun (sc : Suspended) => representative scanFuel sc.var)
      (fun current => current = {before with representatives := current.representatives})
      (first :: rest) ?_ before scanned recorded rfl scan
    intro sc member current root next previous success
    obtain ⟨found, lookup, rootSame, nextSame⟩ := (representative_success scanFuel sc.var current next root).mp success
    rw [nextSame]
    exact congrArg (fun state : State Symbol EnumGuard => {state with representatives := found.forest}) previous
  have unionFrame : united = {before with representatives := united.representatives} := by
    apply forM_invariant (fun (sc : Suspended) => unionVariables unionFuel first.var sc.var)
      (fun current => current = {before with representatives := current.representatives})
      rest ?_ scanned united scanFrame unions
    intro sc member current next previous success
    obtain ⟨forest, lookup, nextSame⟩ := (unionVariables_success unionFuel first.var sc.var current next).mp success
    rw [nextSame]
    exact congrArg (fun state : State Symbol EnumGuard => {state with representatives := forest}) previous
  have afterFrame : after = {before with representatives := after.representatives} := by
    obtain ⟨found, lookup, rootSame, finalSame⟩ := (representative_success rootFuel first.var united after winner).mp resolution
    rw [finalSame]
    exact congrArg (fun state : State Symbol EnumGuard => {state with representatives := found.forest}) unionFrame
  have scanStable : Stable before.counter scanned := by
    apply mapM_invariant (fun (sc : Suspended) => representative scanFuel sc.var)
      (Stable before.counter) (first :: rest) ?_ before scanned recorded ⟨safe.1, rfl⟩ scan
    intro sc member current root next previous success
    exact (representative_stable before.counter scanFuel sc.var root current next previous (bounded sc member) success).1
  have unionStable : Stable before.counter united := by
    apply forM_invariant (fun (sc : Suspended) => unionVariables unionFuel first.var sc.var)
      (Stable before.counter) rest ?_ scanned united scanStable unions
    intro sc member current next previous success
    exact union_stable before.counter unionFuel first.var sc.var current next previous
      (bounded first (by simp)) (bounded sc (List.mem_cons_of_mem first member)) success
  have afterStable : Stable before.counter after := by
    exact (representative_stable before.counter rootFuel first.var winner united after unionStable
      (bounded first (by simp)) resolution).1
  have sameSelected : ∀ (key : Nat), key ∈ recorded ↔ key ∈ selected := by
    intro key
    rw [recordedSame, resolve_members roots rest [roots first.var] key]
    simp [List.mem_map]
  have firstSelected : roots first.var ∈ selected := by
    exact (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
  have winnerRoot : IsRoot after.representatives winner := by
    exact ⟨count, .root (UnionFind.reaches_terminal winnerPath)⟩
  have winnerFixed : roots winner = winner := by
    exact resolved.oldRoots winner winnerRoot
  have winnerSelected : winner ∈ selected := by
    rcases (resolved.joined first.var winner).mp (UnionFind.sameClass_root winnerPath) with same | both
    · simpa [winnerFixed, same] using firstSelected
    · simpa [winnerFixed] using both.2
  have recordedPending : ∀ (source : Nat), source ∈ recorded → PendingAt after source := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, sourceSame⟩ := List.mem_map.mp member
