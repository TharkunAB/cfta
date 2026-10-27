import MicroCFTA.EnumerationFlatReplay
import MicroCFTA.EnumerationFlatNativeIndex

/-!
# Actual terminal-prefix replay with direct-parent forests

Record all old representatives before union. Keep the original raw union
anchor. Move each distinct losing recorded bucket once before assimilation.
-/

namespace MicroCFTA.EnumerationFlatTerminalPrefix

open EnumerationFlatState (Action Related)
open EnumerationFlatReplay
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Record old roots, join original variables, read the winner and move old counts. -/
def run (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) :
    Action Symbol EnumGuard (List Nat × Nat × EnumerationWaitingIndex.Waiting) := do
  let recorded ← (first :: rest).mapM fun sc => EnumerationFlatState.representative sc.var
  rest.forM fun sc => EnumerationFlatState.unionVariables first.var sc.var
  let winner ← EnumerationFlatState.representative first.var
  let sources := EnumerationBuilderCaches.canonicalIds (recorded.filter fun key => key != winner)
  pure (recorded, winner, EnumerationCanonicalWaiting.moveMany winner sources waiting)

/-- Every actual successful earlier prefix has the same flat packet and related final core. -/
theorem run_replays (fuel : Nat) (first : EnumerationState.Suspended)
    (rest : List EnumerationState.Suspended) (waiting : EnumerationWaitingIndex.Waiting) :
    Replays (run (EnumGuard := EnumGuard) first rest waiting)
      (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting) := by
  unfold run SourcePruningEnumerationTerminalPrefix.run
  apply bind_replays _ _ _ _
    (mapM_replays _ _ (fun sc => representative_replays fuel sc.var) (first :: rest))
  intro recorded
  apply bind_replays _ _ _ _
    (forM_replays _ _ (fun sc => union_replays fuel first.var sc.var) rest)
  intro _
  apply bind_replays _ _ _ _ (representative_replays fuel first.var)
  intro winner
  exact pure_replays _

/-- Original admission derives one flat prefix and the same stable earlier completion packet. -/
theorem run_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (flat : EnumerationFlatState.State Symbol EnumGuard)
    (earlier : EnumerationState.State Symbol EnumGuard) (related : Related flat earlier)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (counts : EnumerationCanonicalWaiting.Correct (FlatUnionFind.root flat.representatives) flat.values waiting)
    (safe : EnumerationSchedule.Safe earlier)
    (bounded : ∀ sc ∈ first :: rest, sc.var < flat.counter)
    (pending : EnumerationDependencies.InputsPending earlier (first :: rest))
    (realized : SourcePruningEnumerationObservation.PendingRealized heap earlier) :
    ∃ fuel recorded winner saved scanned united oldAfter after,
      run first rest waiting flat = [.ok ((recorded, winner, saved), after)] ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        (fuel + extra) first rest waiting earlier) = [.ok ((recorded, winner, saved), oldAfter)]) ∧
      Related after oldAfter ∧
      (∀ extra, ExceptT.run (((first :: rest).mapM fun sc =>
        EnumerationState.representative (fuel + extra) sc.var) earlier) = [.ok (recorded, scanned)]) ∧
      (∀ extra, ExceptT.run ((rest.forM fun sc =>
        EnumerationState.unionVariables (fuel + extra) first.var sc.var) scanned) = [.ok ((), united)]) ∧
      (∀ extra, ExceptT.run (EnumerationState.representative (fuel + extra) first.var united) =
        [.ok (winner, oldAfter)]) ∧
      recorded = (first :: rest).map (fun sc => FlatUnionFind.root flat.representatives sc.var) ∧
      saved = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter fun key => key != winner)) waiting ∧
      winner ∈ recorded ∧ FlatUnionFind.root flat.representatives winner = winner ∧
      FlatUnionFind.root after.representatives =
        EnumerationCanonicalUnion.mergedRoots (FlatUnionFind.root flat.representatives) recorded winner ∧
      EnumerationCanonicalWaiting.Correct (FlatUnionFind.root after.representatives) after.values saved ∧
      oldAfter = {earlier with representatives := oldAfter.representatives} ∧
      EnumerationCorrectness.StorageValid oldAfter ∧
      SourcePruningEnumerationObservation.PendingRealized heap oldAfter ∧
      EnumerationCompleteness.PendingAt oldAfter winner ∧
      (∀ source, source ∈ recorded → EnumerationCompleteness.PendingAt oldAfter source) ∧
      (EnumerationBuilderCaches.canonicalIds (recorded.filter fun key => key != winner)).Nodup ∧
      (EnumerationBuilderCaches.canonicalIds (recorded.filter fun key => key != winner)).Pairwise (· ≤ ·) ∧
      (∀ key, key ∈ EnumerationBuilderCaches.canonicalIds (recorded.filter fun key => key != winner) ↔
        key ∈ recorded ∧ key ≠ winner) := by
  have oldCounts : EnumerationCanonicalWaiting.Correct
      (FlatUnionFind.root flat.representatives) earlier.values waiting := by
    simpa only [related.values] using counts
  have oldBounded : ∀ sc ∈ first :: rest, sc.var < earlier.counter := by
    simpa only [related.counter] using bounded
  obtain ⟨fuel, recorded, winner, saved, scanned, united, oldAfter,
    actual, scan, unions, read, recordedSame, savedSame, winnerMember, winnerFixed,
    paths, finalCounts, afterSame, storage, finalRealized, winnerPending, sourcesPending,
    nodup, ordered, keys⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_complete heap earlier first rest waiting
      (FlatUnionFind.root flat.representatives)
      (EnumerationFlatNativeIndex.related_roots related.representatives)
      oldCounts safe oldBounded pending realized
  have oldSuccess : EnumerationCorrectness.Success
      (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting) earlier
      (recorded, winner, saved) oldAfter := by
    have exactRun := actual 0
    simp only [Nat.add_zero] at exactRun
    simp only [EnumerationCorrectness.Success, exactRun, List.mem_singleton]
  obtain ⟨after, flatRun, finalRelated⟩ :=
    run_replays fuel first rest waiting flat earlier (recorded, winner, saved) oldAfter related oldSuccess
  have roots : FlatUnionFind.root after.representatives =
      EnumerationCanonicalUnion.mergedRoots (FlatUnionFind.root flat.representatives) recorded winner := by
    funext uv
    obtain ⟨size, path⟩ := paths uv
    exact (UnionFind.reaches_unique (finalRelated.representatives uv) path).1
  have flatCounts : EnumerationCanonicalWaiting.Correct
      (FlatUnionFind.root after.representatives) after.values saved := by
    rw [roots, finalRelated.values]
    exact finalCounts
  exact ⟨fuel, recorded, winner, saved, scanned, united, oldAfter, after,
    flatRun, actual, finalRelated, scan, unions, read, recordedSame, savedSame,
    winnerMember, winnerFixed, roots, flatCounts, afterSame, storage, finalRealized,
    winnerPending, sourcesPending, nodup, ordered, keys⟩

/-- Retain the expandable flags and install the actual completed prefix count table. -/
def cached (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (before : EnumerationFlatCached.Cached Symbol EnumGuard) :
    List (Except EnumerationState.Error
      ((List Nat × Nat) × EnumerationFlatCached.Cached Symbol EnumGuard)) :=
  (ExceptT.run (run first rest before.waiting before.core)).map fun row =>
    match row with
    | .error error => .error error
    | .ok ((recorded, winner, moved), after) =>
        .ok ((recorded, winner), ⟨after, before.expandable, moved⟩)

/-- The same actual cached prefix derives its final native indexes and earlier pending packet. -/
theorem cached_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (flat : EnumerationFlatCached.Cached Symbol EnumGuard)
    (earlier : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (related : EnumerationFlatCached.Related flat earlier)
    (correct : EnumerationFlatNativeIndex.Correct heap flat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (safe : EnumerationSchedule.Safe earlier.core)
    (bounded : ∀ sc ∈ first :: rest, sc.var < flat.core.counter)
    (pending : EnumerationDependencies.InputsPending earlier.core (first :: rest))
    (realized : SourcePruningEnumerationObservation.PendingRealized heap earlier.core) :
    ∃ fuel recorded winner after oldAfter,
      cached first rest flat = [.ok ((recorded, winner), after)] ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        (fuel + extra) first rest earlier.waiting earlier.core) =
        [.ok ((recorded, winner, after.waiting), oldAfter.core)]) ∧
      EnumerationFlatCached.Related after oldAfter ∧ EnumerationFlatNativeIndex.Correct heap after ∧
      after.expandable = flat.expandable ∧ oldAfter.expandable = earlier.expandable ∧
      oldAfter.waiting = after.waiting ∧
      recorded = (first :: rest).map (fun sc => FlatUnionFind.root flat.core.representatives sc.var) ∧
      after.waiting = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter fun key => key != winner)) flat.waiting ∧
      winner ∈ recorded ∧
      EnumerationCorrectness.StorageValid oldAfter.core ∧
      SourcePruningEnumerationObservation.PendingRealized heap oldAfter.core ∧
      EnumerationCompleteness.PendingAt oldAfter.core winner ∧
      (∀ source, source ∈ recorded → EnumerationCompleteness.PendingAt oldAfter.core source) := by
  obtain ⟨fuel, recorded, winner, saved, _scanned, _united, oldAfter, after,
    flatRun, oldRun, finalRelated, _scan, _unions, _read, recordedSame, savedSame,
    winnerMember, _winnerFixed, _roots, counts, afterSame, storage, finalRealized,
    winnerPending, sourcesPending, _nodup, _ordered, _keys⟩ :=
    run_complete heap flat.core earlier.core related.core first rest flat.waiting
      correct.waiting safe bounded pending realized
  have values : after.values = flat.core.values := by
    rw [finalRelated.values, afterSame]
    exact related.core.values.symm
  have counter : after.counter = flat.core.counter := by
    rw [finalRelated.counter, afterSame]
    exact related.core.counter.symm
  let next : EnumerationFlatCached.Cached Symbol EnumGuard := ⟨after, flat.expandable, saved⟩
  let oldNext : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
    ⟨oldAfter, earlier.expandable, saved⟩
  have nextCorrect : EnumerationFlatNativeIndex.Correct heap next := by
    refine ⟨?_, ?_, counts⟩
    · change after.counter = after.values.length
      rw [counter, values]
      exact correct.aligned
    · intro uv
      simpa only [next, values] using correct.expandable uv
  refine ⟨fuel, recorded, winner, next, oldNext, ?_, ?_,
    ⟨finalRelated, related.expandable, rfl⟩, nextCorrect, rfl, rfl, rfl,
    recordedSame, savedSame, winnerMember, storage, finalRealized, winnerPending, sourcesPending⟩
  · simp only [cached, ExceptT.run, flatRun, List.map_cons, List.map_nil]
    rfl
  · intro extra
    rw [← related.waiting]
    exact oldRun extra

end MicroCFTA.EnumerationFlatTerminalPrefix
