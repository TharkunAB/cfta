import MicroCFTA.EnumerationCompleteness
import MicroCFTA.EnumerationCanonicalUnion
import MicroCFTA.EnumerationBuilderCaches
import MicroCFTA.SourcePruningEnumerationObservation

namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution
open EnumerationCompleteness EnumerationDependencies
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance terminalPrefixMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance terminalPrefixLawfulMonadList : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- Record original roots, join their classes and transfer the old waiting buckets. -/
def run (fuel : Nat) (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) :
    EnumerateM Symbol EnumGuard (List Nat × Nat × EnumerationWaitingIndex.Waiting) := do
  let recorded ← (first :: rest).mapM fun sc => representative fuel sc.var
  rest.forM fun sc => unionVariables fuel first.var sc.var
  let winner ← representative fuel first.var
  let sources : List Nat :=
    EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))
  pure (recorded, winner, EnumerationCanonicalWaiting.moveMany winner sources waiting)

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
    obtain ⟨size, path⟩ := paths sc.var
    obtain ⟨node, scs, stored⟩ := inputs_pendingAt before safe (first :: rest) bounded pending sc present (roots sc.var) size path
    exact ⟨node, scs, by simpa only [resolved.values, ← sourceSame] using stored⟩
  let keys : List Nat := EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))
  have keyMembers : ∀ (key : Nat), key ∈ keys ↔ key ∈ recorded ∧ key ≠ winner := by
    intro key
    simp [keys, EnumerationBuilderCaches.canonicalIds_member]
  have actualRoots : Roots after.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) := by
    intro uv
    simpa only [EnumerationCanonicalUnion.mergedRoots, ← sameSelected] using
      EnumerationCanonicalUnion.merging_roots before.values roots selected after resolved first.var winner count firstSelected winnerPath uv
  have finalCounts : EnumerationCanonicalWaiting.Correct
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) after.values
      (EnumerationCanonicalWaiting.moveMany winner keys waiting) := by
    rw [resolved.values, ← EnumerationCanonicalUnion.redirect_fold_eq roots recorded winner keys keyMembers]
    exact EnumerationCanonicalWaiting.moveMany_correct winner keys roots before.values waiting counts
  have finalRealized : PendingRealized heap after := by
    intro slot node scs stored
    exact realized slot node scs (by simpa only [resolved.values] using stored)
  let fuel : Nat := scanFuel + unionFuel + rootFuel
  have scanMore : ∀ (extra : Nat), Success ((first :: rest).mapM fun sc =>
      representative (fuel + extra) sc.var) before recorded scanned := by
    intro extra
    simpa [fuel, Nat.add_assoc] using retains_mapM _ _ (fun (sc : Suspended) =>
      representative_moreFuel scanFuel (unionFuel + rootFuel + extra) sc.var) (first :: rest) _ _ _ scan
  have unionsMore : ∀ (extra : Nat), Success (rest.forM fun sc =>
      unionVariables (fuel + extra) first.var sc.var) scanned () united := by
    intro extra
    simpa [fuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using retains_forM _ _ (fun (sc : Suspended) =>
      unionVariables_moreFuel unionFuel (scanFuel + rootFuel + extra) first.var sc.var) rest _ _ _ unions
  have resolutionMore : ∀ (extra : Nat), Success (representative (fuel + extra) first.var)
      united winner after := by
    intro extra
    simpa [fuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      representative_moreFuel rootFuel (scanFuel + unionFuel + extra) first.var _ _ _ resolution
  refine ⟨fuel, recorded, winner, EnumerationCanonicalWaiting.moveMany winner keys waiting,
    scanned, united, after, ?_, ?_, ?_, ?_, recordedSame, rfl,
    (sameSelected winner).mpr winnerSelected, winnerFixed, actualRoots, finalCounts, afterFrame,
    afterStable.1, finalRealized, recordedPending winner ((sameSelected winner).mpr winnerSelected),
    recordedPending, EnumerationBuilderCaches.canonicalIds_nodup _,
    EnumerationBuilderCaches.canonicalIds_sorted _, keyMembers⟩
  · intro extra
    unfold run
    rw [bind_single _ _ before scanned recorded (scanExact _ _ _ _ _ (scanMore extra))]
    rw [bind_single _ _ scanned united () (unionsExact _ _ _ _ _ (unionsMore extra))]
    obtain ⟨found, lookup, rootSame, finalSame⟩ :=
      (representative_success (fuel + extra) first.var united after winner).mp (resolutionMore extra)
    rw [bind_single _ _ united after winner
      (by simpa only [← rootSame, ← finalSame] using representative_exact (fuel + extra) first.var united found lookup)]
    rfl
  · intro extra
    exact scanExact _ _ _ _ _ (scanMore extra)
  · intro extra
    exact unionsExact _ _ _ _ _ (unionsMore extra)
  · intro extra
    obtain ⟨found, lookup, rootSame, finalSame⟩ :=
      (representative_success (fuel + extra) first.var united after winner).mp (resolutionMore extra)
    simpa only [← rootSame, ← finalSame, ExceptT.run] using representative_exact (fuel + extra) first.var united found lookup

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
