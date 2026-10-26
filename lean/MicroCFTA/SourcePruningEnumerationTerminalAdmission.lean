import MicroCFTA.SourcePruningEnumerationTerminalPrefixUnique
import MicroCFTA.SourcePruningEnumerationFoldUnique
import MicroCFTA.SourcePruningEnumerationFoldResources
import MicroCFTA.SourcePruningEnumerationIncomingNodeResources
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter

/-!
# Original resource admission for actual terminal requests

Every successful prefix agrees with the prefix derived from current facts.
Every successful fold agrees with its derived completion. The original
mixed reservation gives Room for that fold and its following incoming
query. These statements require no future range or success premise.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationCompleteness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {EnumGuard : Type} {bits : Nat}

/-- Every actual successful prefix retains its recorded roots and realized pending slots. -/
theorem observed_prefix
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationState.State Symbol EnumGuard)
    (first : Suspended) (rest : List Suspended) (waiting : EnumerationWaitingIndex.Waiting)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (safe : Safe before) (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest)) (realized : PendingRealized heap before)
    {fuel : Nat} {recorded : List Nat} {winner : Nat} {moved : EnumerationWaitingIndex.Waiting}
    {joined : EnumerationState.State Symbol EnumGuard}
    (observed : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting before) =
      [.ok ((recorded, winner, moved), joined)]) :
    recorded = (first :: rest).map (fun sc => roots sc.var) ∧ PendingRealized heap joined ∧
      PendingAt joined winner ∧ ∀ source ∈ recorded, PendingAt joined source := by
  obtain ⟨n, actualRecorded, actualWinner, actualMoved, _scanned, _united, actualJoined,
    stable, _scan, _unions, _winner, recordedSame, _movedSame, _winnerMember, _rootWinner,
    _afterRoots, _afterCounts, _joinedSame, _storage, joinedRealized, winnerPending,
    recordedPending, _nodup, _sorted, _members⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_complete heap before first rest waiting roots
      paths counts safe bounded pending realized
  have actual := stable 0
  simp only [Nat.add_zero] at actual
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourcePruningEnumerationTerminalPrefix.run_unique
    first rest waiting before observed actual
  exact ⟨recordedSame, joinedRealized, winnerPending, recordedPending⟩

/-- Original current facts and one mixed reservation derive all terminal range predicates. -/
theorem initial_ranges
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checkEmpty : Bool) (first : Suspended) (rest : List Suspended)
    (incoming : Node) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed ((first :: rest).length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    Ranges checkEmpty first rest beforeCaller before incoming memos.query := by
  intro prefixFuel recorded winner moved joined prefixObserved
  obtain ⟨recordedSame, joinedRealized, winnerPending, recordedPending⟩ :=
    observed_prefix beforeCaller.checked.native.machine.heap before.core first rest before.waiting roots
      paths counts safe bounded pending realized prefixObserved
  have lengthSame : recorded.length = (first :: rest).length := by
    simp only [recordedSame, List.length_map]
  have reservation : Reserved bits seed (recorded.length + 1) := by
    simpa only [lengthSame] using reserved
  have foldReservation : Reserved bits seed recorded.length := reservation.prefix (by omega)
  have selected : ∀ source ∈ recorded, PendingOrEliminated joined source :=
    fun source member => .inl (recordedPending source member)
  have foldRanges := SourcePruningEnumerationFold.initial_ranges seed formulas solver inventory
    beforeCaller joined recorded checkEmpty winner memos initial joinedRealized winnerPending selected
    fits foldReservation known
  refine ⟨foldRanges, ?_⟩
  intro foldFuel P H foldCaller folded foldQueries observedFold
  obtain ⟨n, lowP, lowH, raw, actualCaller, actualCore, actualQueries, final, next, stable,
    post, _querySame, finalRealized, _shape, _completed, _eliminated, _length, _forest,
    _counter, _obligations, _expansion, _ancestry, _rejection⟩ :=
    SourcePruningEnumerationFold.run_complete formulas solver inventory beforeCaller joined recorded
      checkEmpty winner memos initial joinedRealized winnerPending
      (fun source member => .inr (recordedPending source member)) foldRanges
  have actual := stable 0 lowP lowH (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  obtain ⟨_rawSame, callerSame, _queriesSame, coreSame⟩ :=
    SourcePruningEnumerationFold.ok_unique checkEmpty actual observedFold
  subst actualCaller
  subst actualCore
  have resources := SourcePruningEnumerationFold.observed_resources seed formulas solver inventory
    beforeCaller joined recorded checkEmpty foldFuel P H winner memos initial joinedRealized
    winnerPending selected fits foldReservation known observedFold
  have remaining : Reserved bits (advance seed recorded.length) 1 := reservation.after_prefix
  exact SourcePruningEnumerationIncomingNode.initial_ranges (advance seed recorded.length).2
    foldCaller folded winner incoming post.context.ready finalRealized
    (post.effects.keeps.available incoming available) closed resources.1 remaining.head

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
