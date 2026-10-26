import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.EnumerationSemantics

/-!
# Exact assignments and joined classes of the actual terminal prefix

The original prefix runs once. Its complete receipt remains available.
Its actual root paths equate every recorded source with the winner.
Its actual union loop adds exactly the requested assignment equations.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution
open EnumerationCompleteness EnumerationDependencies
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- The actual prefix supplies the class equality and exact assignments used by assimilation. -/
theorem run_complete_semantics
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
        key ∈ recorded ∧ key ≠ winner) ∧
      (∀ source ∈ recorded, UnionFind.SameClass after.representatives source winner) ∧
      ∀ (language : NodeLanguage Symbol) (meaning : EnumGuard → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before ∧
          ∀ sc ∈ rest, assignment first.var = assignment sc.var := by
  obtain ⟨fuel, recorded, winner, saved, scanned, united, after, running, scanning, unions, resolution,
    recordedSame, savedSame, winnerMember, winnerFixed, afterPaths, afterCounts, afterSame,
    afterStorage, afterRealized, winnerPending, sourcesPending, distinct, ordered, keys⟩ :=
    run_complete heap before first rest waiting roots paths counts safe bounded pending realized
  refine ⟨fuel, recorded, winner, saved, scanned, united, after, running, scanning, unions, resolution,
    recordedSame, savedSame, winnerMember, winnerFixed, afterPaths, afterCounts, afterSame,
    afterStorage, afterRealized, winnerPending, sourcesPending, distinct, ordered, keys, ?_, ?_⟩
  · intro source member
    have sourceFixed : roots source = source := by
      rw [recordedSame] at member
      obtain ⟨sc, _present, rfl⟩ := List.mem_map.mp member
      exact EnumerationCanonicalUnion.roots_idempotent before.representatives roots paths sc.var
    have sourceSelected : roots source ∈ recorded := by simpa only [sourceFixed] using member
    have winnerSelected : roots winner ∈ recorded := by simpa only [winnerFixed] using winnerMember
    apply (class_iff after.representatives
      (EnumerationCanonicalUnion.mergedRoots roots recorded winner) afterPaths source winner).mpr
    simp only [EnumerationCanonicalUnion.mergedRoots, ite_eq_left sourceSelected, ite_eq_left winnerSelected]
  · intro language meaning assignment
    have scanSuccess : Success ((first :: rest).mapM fun sc => representative fuel sc.var)
        before recorded scanned := by
      have actual := scanning 0
      simp only [Nat.add_zero] at actual
      rw [Success, actual]
      exact List.mem_singleton_self _
    have unionSuccess : Success (rest.forM fun sc => unionVariables fuel first.var sc.var)
        scanned () united := by
      have actual := unions 0
      simp only [Nat.add_zero] at actual
      rw [Success, actual]
      exact List.mem_singleton_self _
    have rootSuccess : Success (representative fuel first.var) united winner after := by
      have actual := resolution 0
      simp only [Nat.add_zero] at actual
      rw [Success, actual]
      exact List.mem_singleton_self _
    obtain ⟨scannedTotal, scanMeaning⟩ := EnumerationSemantics.representatives_assignment
      language meaning assignment fuel (first :: rest) before scanned recorded safe.1.total scanSuccess
    obtain ⟨unitedTotal, unionMeaning⟩ := EnumerationSemantics.terminal_unions_assignment
      language meaning assignment fuel first.var rest scanned united scannedTotal unionSuccess
    have rootMeaning := (EnumerationSemantics.representative_assignment language meaning assignment
      fuel first.var winner united after unitedTotal rootSuccess).2
    exact rootMeaning.trans (unionMeaning.trans (and_congr_left fun _ => scanMeaning))

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
