import MicroCFTA.SourceCurrentAllocatedNativeFoldIncomingEntry
import MicroCFTA.SourceCurrentAllocatedNativeCachedFoldKnown
import MicroCFTA.SourceCurrentAllocatedNativeIncomingCacheKnown
import MicroCFTA.SourcePruningEnumerationTerminalPrefixUnique
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter

/-!
# Whole ordinary bounds for the actual terminal adapter

Incoming cache execution uses the current ordinary-value bounds.
Current incoming domain and height remain explicit. Source-builder admission is separate.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativeTerminalKnown
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

private theorem prefix_admission (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : Core) (first : Suspended) (rest : List Suspended) (waiting : EnumerationWaitingIndex.Waiting)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (safe : Safe before) (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest)) (realized : PendingRealized heap before)
    {r : Nat} {recorded : List Nat} {winner : Nat} {moved : EnumerationWaitingIndex.Waiting} {joined : Core}
    (observed : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) =
      [.ok ((recorded, winner, moved), joined)]) :
    recorded = (first :: rest).map (fun sc => roots sc.var) ∧ joined.values = before.values ∧
      PendingRealized heap joined ∧ PendingAt joined winner ∧ ∀ source ∈ recorded, PendingAt joined source := by
  obtain ⟨r0, actualRecorded, actualWinner, actualMoved, _scanned, _united, _after,
    stable, _scan, _unions, _read, recordedSame, _movedSame, _member, _root, _roots, _counts,
    afterSame, _storage, afterRealized, afterPending, sourcesPending, _nodup, _sorted, _members⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_complete heap before first rest waiting roots paths counts safe bounded pending realized
  have actual := stable 0
  simp only [Nat.add_zero] at actual
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourcePruningEnumerationTerminalPrefix.run_unique first rest waiting before observed actual
  exact ⟨recordedSame, by rw [afterSame], afterRealized, afterPending, sourcesPending⟩

private theorem map_known {bound winner : Nat} {heap : InternedConstructorTemplates.State Symbol Constraint}
    {before : Cached} {rows : Raw}
    (rowKnown : ∀ returned : Core, Except.ok ((), returned) ∈ rows → KnownOrdinary bound heap {before with core := returned}) :
    ∀ (fragment : Fragments.Fragment Symbol) (returned : Core), Except.ok (fragment, returned) ∈ rows.map (fun row => match row with
      | .error fault => .error fault | .ok result => .ok (.hole winner, result.2)) →
      KnownOrdinary bound heap {before with core := returned} := by
  intro fragment returned member
  obtain ⟨row, inRows, same⟩ := List.mem_map.mp member
  cases row with
  | error _fault => simp at same
  | ok pair =>
      rcases pair with ⟨valueUnit, current⟩
      cases valueUnit
      simp only [Except.ok.injEq, Prod.mk.injEq] at same
      rcases same with ⟨_fragmentSame, rfl⟩
      exact rowKnown current inRows

variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- Actual successful terminal Core rows and every returned cache keep the same whole ordinary cap. -/
theorem run_known (bits bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h indexFuel : Nat) (first : Suspended) (rest : List Suspended)
    (incoming : Node) (incomingScs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingDomain : NodeDomain incoming) (incomingHeight : MergedOrdinaryHeight.height incoming ≤ bound)
    (fits : Fits seed.2 beforeCaller.checked) (reserved : Reserved bits seed ((first :: rest).length + 1))
    (annotated : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (stored : Stored beforeCaller.checked.native)
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before) :
    let actual := SourcePruningEnumerationCachedTerminalAdapter.run checkEmpty r n p h indexFuel
      first rest beforeCaller before incoming incomingScs memos.query
    (match actual.1.1 with
      | .ok (some rows) => ∀ fragment returned, Except.ok (fragment, returned) ∈ rows →
          KnownOrdinary bound actual.1.2.1.checked.native.machine.heap {before with core := returned}
      | _ => True) ∧
    (match actual.2 with
      | some after => KnownOrdinary bound actual.1.2.1.checked.native.machine.heap after
      | none => True) := by
  classical
  by_cases empty : incoming = .empty
  · simpa [SourcePruningEnumerationCachedTerminalAdapter.run, empty] using known
  · cases prefixEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting before.core) with
    | nil => simp [SourcePruningEnumerationCachedTerminalAdapter.run, empty, prefixEq]
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error _fault => simp [SourcePruningEnumerationCachedTerminalAdapter.run, empty, prefixEq]
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
        cases prefixTail with
        | cons _next _rest => simp [SourcePruningEnumerationCachedTerminalAdapter.run, empty, prefixEq]
        | nil =>
          obtain ⟨recordedSame, valuesSame, joinedRealized, winnerPending, sourcesPending⟩ :=
            prefix_admission beforeCaller.checked.native.machine.heap before.core first rest before.waiting roots
              paths counts safe bounded pending realized prefixEq
          have lengthSame : recorded.length = (first :: rest).length := by simp only [recordedSame, List.length_map]
          have reservation : Reserved bits seed (recorded.length + 1) := by simpa only [lengthSame] using reserved
          have joinedKnown : KnownOrdinary bound beforeCaller.checked.native.machine.heap ⟨joined, before.expandable, moved⟩ := by
            simpa only [KnownOrdinary, valuesSame] using known
          have selected : ∀ source ∈ recorded, PendingOrEliminated joined source := fun source member => Or.inl (sourcesPending source member)
          have cacheKnown := SourceCurrentAllocatedNativeCachedFoldKnown.fold_known bits bound seed formulas solver inventory
            beforeCaller ⟨joined, before.expandable, moved⟩ recorded checkEmpty n p h winner memos initial joinedRealized winnerPending
            selected fits (reservation.prefix (Nat.le_succ _)) annotated stored joinedKnown
          cases foldEq : SourcePruningEnumerationCachedFold.run checkEmpty n p h recorded
              beforeCaller ⟨joined, before.expandable, moved⟩ winner memos.query with
          | mk foldObservation foldCache =>
            rcases foldObservation with ⟨foldTag, foldCaller, foldQueries, foldOuter⟩
            simp only [SourcePruningEnumerationCachedTerminalAdapter.run, ite_eq_right empty, prefixEq, foldEq]
            cases foldTag with
            | error _fault => exact ⟨trivial, trivial⟩
            | ok possible =>
              cases possible with
              | none => exact ⟨trivial, trivial⟩
              | some foldRows =>
                cases foldRows with
                | nil =>
                  refine ⟨?_, ?_⟩
                  · intro fragment returned member; cases member
                  · cases foldCache <;> simp only [foldEq] at cacheKnown <;> exact cacheKnown
                | cons foldEntry foldTail =>
                  cases foldEntry with
                  | error _fault => exact ⟨trivial, trivial⟩
                  | ok pair =>
                    rcases pair with ⟨valueUnit, folded⟩
                    cases valueUnit
                    cases foldTail with
                    | cons _next _rest => exact ⟨trivial, trivial⟩
                    | nil =>
                      have foldRaw : SourcePruningEnumerationFold.run checkEmpty n p h recorded beforeCaller joined winner memos.query =
                          (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, foldOuter) := by
                        rw [← SourcePruningEnumerationCachedFold.erase checkEmpty n p h recorded
                          beforeCaller ⟨joined, before.expandable, moved⟩ winner memos.query, foldEq]
                      have entry := SourceCurrentAllocatedNativeFoldIncomingEntry.fold_incoming_entry bits bound seed formulas solver inventory
                        beforeCaller ⟨joined, before.expandable, moved⟩ recorded checkEmpty n p h winner memos incoming initial joinedRealized
                        winnerPending selected fits reservation annotated stored joinedKnown available
                      simp only [foldRaw] at entry
                      obtain ⟨next, final, post, _querySame, afterRealized, _afterPending, afterFits, afterRoom,
                        _afterHeap, afterStored, afterKnown, incomingAvailable⟩ := entry
                      cases foldCache with
                      | none =>
                        dsimp only
                        have rowsKnown := SourceCurrentAllocatedNativeIncomingKnown.run_known bits bound (advance seed recorded.length).2
                          formulas solver next foldCaller {before with core := folded} checkEmpty r n p h winner incoming incomingScs final foldQueries
                          post.context afterRealized incomingAvailable closed incomingDomain incomingHeight afterKnown afterFits afterRoom afterStored
                        cases incomingEq : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h foldCaller folded winner incoming incomingScs foldQueries with
                        | mk tag tail =>
                          rcases tail with ⟨afterCaller, savedQueries, read⟩
                          simp only
                          cases tag with
                          | error _fault => exact ⟨trivial, trivial⟩
                          | ok possible =>
                            cases possible with
                            | none => exact ⟨trivial, trivial⟩
                            | some rows =>
                              have rowBounds : ∀ returned : Core, Except.ok ((), returned) ∈ rows →
                                  KnownOrdinary bound afterCaller.checked.native.machine.heap {before with core := returned} := by
                                simpa only [incomingEq] using rowsKnown.2
                              exact ⟨map_known (winner := winner) (before := before) rowBounds, trivial⟩
                      | some recovered =>
                        dsimp only
                        have incomingKnown := SourceCurrentAllocatedNativeIncomingCacheKnown.run_known bits bound (advance seed recorded.length).2
                          formulas solver next foldCaller (EnumerationExpandableIndex.frame folded recovered) checkEmpty r n p h indexFuel winner
                          incoming incomingScs final foldQueries post.context afterRealized incomingAvailable closed incomingDomain incomingHeight
                          afterKnown afterFits afterRoom afterStored
                        cases incomingEq : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h indexFuel foldCaller
                            (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs foldQueries with
                        | mk observation incomingCache =>
                          rcases observation with ⟨tag, afterCaller, savedQueries, read⟩
                          simp only
                          cases tag with
                          | error _fault => exact ⟨trivial, trivial⟩
                          | ok possible =>
                            cases possible with
                            | none => exact ⟨trivial, trivial⟩
                            | some rows =>
                              have both := incomingKnown
                              simp only [incomingEq] at both
                              exact ⟨map_known (winner := winner) (before := before) both.1, both.2⟩

end MicroCFTA.SourceCurrentAllocatedNativeTerminalKnown
