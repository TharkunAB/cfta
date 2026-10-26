import MicroCFTA.SourcePruningEnumerationTerminalPrefixLanguage
import MicroCFTA.SourcePruningEnumerationTerminalPrefixUnique

/-!
# Assignment receipts at the actual terminal-prefix endpoint

One canonical prefix receipt identifies every returned field.
The actual joined core retains its stored slots and exact assignment equations.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Retain the pending slots, joined classes and exact meaning of an actual prefix observation. -/
theorem observed_semantics
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (roots : Nat → Nat)
    (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (safe : Safe before)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest))
    (realized : PendingRealized heap before)
    {prefixFuel : Nat} {recorded : List Nat} {winner : Nat}
    {moved : EnumerationWaitingIndex.Waiting}
    {joined : EnumerationState.State Symbol EnumGuard}
    (observed : ExceptT.run (run prefixFuel first rest waiting before) =
      [.ok ((recorded, winner, moved), joined)]) :
    joined = {before with representatives := joined.representatives} ∧
    StorageValid joined ∧ PendingRealized heap joined ∧ PendingAt joined winner ∧
    (∀ source ∈ recorded, PendingAt joined source) ∧
    (∀ source ∈ recorded, UnionFind.SameClass joined.representatives source winner) ∧
    Roots joined.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
    ∀ (language : NodeLanguage Symbol) (meaning : EnumGuard → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      Satisfies language meaning assignment joined ↔ Satisfies language meaning assignment before ∧
        ∀ sc ∈ rest, assignment first.var = assignment sc.var := by
  obtain ⟨fuel, canonicalRecorded, canonicalWinner, canonicalMoved, _scanned, _united,
    canonicalJoined, running, _scanning, _unions, _resolution, _recordedSame, _movedSame,
    _winnerMember, _winnerFixed, joinedPaths, _joinedCounts, joinedSame, joinedStorage,
    joinedRealized, winnerPending, sourcesPending, _distinct, _ordered, _keys,
    classes, semantic⟩ :=
      run_complete_semantics heap before first rest waiting roots paths counts safe bounded pending realized
  have canonicalObserved : ExceptT.run (run fuel first rest waiting before) =
      [.ok ((canonicalRecorded, canonicalWinner, canonicalMoved), canonicalJoined)] := by
    simpa only [Nat.add_zero] using running 0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := run_unique first rest waiting before observed canonicalObserved
  exact ⟨joinedSame, joinedStorage, joinedRealized, winnerPending, sourcesPending,
    classes, joinedPaths, semantic⟩

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
