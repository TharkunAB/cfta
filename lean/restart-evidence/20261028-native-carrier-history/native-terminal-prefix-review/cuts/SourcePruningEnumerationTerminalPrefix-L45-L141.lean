/-- Genuine initial invariants derive the exact prefix at every sufficient fuel. -/
theorem run_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (roots : Nat → Nat)
    (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (safe : Safe before)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest))
    (realized : PendingRealized heap before) :
    ∃ (fuel : Nat) (recorded : List Nat) (winner : Nat) (saved : EnumerationWaitingIndex.Waiting)
      (scanned united after : EnumerationState.State Symbol EnumGuard),
      (∀ (extra : Nat), ExceptT.run (run (fuel + extra) first rest waiting before) =
        [.ok ((recorded, winner, saved), after)]) ∧
      (∀ (extra : Nat), ExceptT.run (((first :: rest).mapM fun sc =>
        representative (fuel + extra) sc.var) before) = [.ok (recorded, scanned)]) ∧
      (∀ (extra : Nat), ExceptT.run ((rest.forM fun sc =>
        unionVariables (fuel + extra) first.var sc.var) scanned) = [.ok ((), united)]) ∧
      (∀ (extra : Nat), ExceptT.run (representative (fuel + extra) first.var united) = [.ok (winner, after)]) ∧
      recorded = (first :: rest).map (fun sc => roots sc.var) ∧
      saved = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))) waiting ∧
      winner ∈ recorded ∧ roots winner = winner ∧
      Roots after.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        after.values saved ∧
      after = {before with representatives := after.representatives} ∧
      StorageValid after ∧ PendingRealized heap after ∧ PendingAt after winner ∧
      (∀ (source : Nat), source ∈ recorded → PendingAt after source) ∧
      (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))).Nodup ∧
      (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))).Pairwise (· ≤ ·) ∧
      (∀ (key : Nat), key ∈ EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner)) ↔
        key ∈ recorded ∧ key ≠ winner) := by
  have scanExact : ∀ (fuel : Nat) (items : List EnumerationState.Suspended)
      (entry exit : EnumerationState.State Symbol EnumGuard) (recorded : List Nat),
      Success (items.mapM fun sc => representative fuel sc.var) entry recorded exit →
      ExceptT.run ((items.mapM fun sc => representative fuel sc.var) entry) = [.ok (recorded, exit)] := by
    intro fuel items
    induction items with
    | nil =>
        intro entry exit recorded observed
        obtain ⟨valueSame, stateSame⟩ := (success_pure [] recorded entry exit).mp observed
        rw [valueSame, stateSame]
        rfl
    | cons sc items ih =>
        intro entry exit recorded observed
        rw [List.mapM_cons] at observed ⊢
        obtain ⟨root, middle, head, continued⟩ := (success_bind _ _ _ _ _).mp observed
        obtain ⟨tail, last, tailRun, finalPure⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨valueSame, stateSame⟩ := (success_pure (root :: tail) recorded last exit).mp finalPure
        obtain ⟨found, lookup, rootSame, middleSame⟩ :=
          (representative_success fuel sc.var entry middle root).mp head
        rw [bind_single _ _ entry middle root
          (by simpa only [← rootSame, ← middleSame] using representative_exact fuel sc.var entry found lookup)]
        rw [bind_single _ _ middle last tail (ih middle last tail tailRun)]
        rw [valueSame, stateSame]
        rfl
  have unionsExact : ∀ (fuel anchor : Nat) (items : List EnumerationState.Suspended)
      (entry exit : EnumerationState.State Symbol EnumGuard),
      Success (items.forM fun sc => unionVariables fuel anchor sc.var) entry () exit →
      ExceptT.run ((items.forM fun sc => unionVariables fuel anchor sc.var) entry) = [.ok ((), exit)] := by
    intro fuel anchor items
    induction items with
    | nil =>
        intro entry exit observed
        obtain ⟨valueSame, stateSame⟩ := (success_pure () () entry exit).mp observed
        rw [stateSame]
        rfl
    | cons sc items ih =>
        intro entry exit observed
        change Success (unionVariables fuel anchor sc.var >>= fun _ =>
          items.forM fun sc => unionVariables fuel anchor sc.var) entry () exit at observed
        obtain ⟨ignored, middle, head, continued⟩ := (success_bind _ _ _ _ _).mp observed
        cases ignored
        obtain ⟨forest, lookup, middleSame⟩ := (unionVariables_success fuel anchor sc.var entry middle).mp head
        change ExceptT.run ((unionVariables fuel anchor sc.var >>= fun _ =>
          items.forM fun sc => unionVariables fuel anchor sc.var) entry) = [.ok ((), exit)]
        rw [bind_single _ _ entry middle ()
          (by simpa only [← middleSame] using union_exact fuel anchor sc.var entry forest lookup)]
        exact ih middle exit continued
  obtain ⟨scanFuel, recorded, scanned, scan, scanTotal⟩ := mapM_terminates
    (fun fuel (sc : Suspended) => representative fuel sc.var)
    (fun state : State Symbol EnumGuard => UnionFind.Total state.representatives)
    (fun fuel extra sc => representative_moreFuel fuel extra sc.var)
    (fun sc state valid => representative_terminates state valid sc.var)
    (first :: rest) before safe.1.total
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots scanFuel
    (first :: rest) before scanned recorded ⟨rfl, paths⟩ scan
  obtain ⟨unionFuel, united, unions, unionTotal⟩ := forM_terminates
    (fun fuel (sc : Suspended) => unionVariables fuel first.var sc.var)
    (fun state : State Symbol EnumGuard => UnionFind.Total state.representatives)
    (fun fuel extra sc => unionVariables_moreFuel fuel extra first.var sc.var)
    (fun sc state valid => unionVariables_terminates state valid first.var sc.var)
    rest scanned scanTotal
  let selected : List Nat := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
