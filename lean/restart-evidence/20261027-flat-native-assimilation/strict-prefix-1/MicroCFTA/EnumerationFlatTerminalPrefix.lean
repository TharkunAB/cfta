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
    (safe : EnumerationCorrectness.Safe earlier)
    (bounded : ∀ sc ∈ first :: rest, sc.var < flat.counter)
    (pending : EnumerationSchedule.InputsPending earlier (first :: rest))
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
      EnumerationSchedule.PendingAt oldAfter winner ∧
      (∀ source, source ∈ recorded → EnumerationSchedule.PendingAt oldAfter source) ∧
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

end MicroCFTA.EnumerationFlatTerminalPrefix
