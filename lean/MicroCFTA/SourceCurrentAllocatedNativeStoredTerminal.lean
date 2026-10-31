import MicroCFTA.SourceCurrentAllocatedNativeStoredFold
import MicroCFTA.SourceCurrentAllocatedNativeStoredIncoming
import MicroCFTA.SourcePruningEnumerationTerminalObservedResources

/-!
# Native structural certificates at every actual terminal return

Current prefix and reservation facts derive the actual later entry properties.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationCompleteness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual terminal outcome retains native certificates under its current reservation. -/
theorem terminal_native_stored (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (incoming : Node) (incomingScs : List Suspended)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before) (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed ((first :: rest).length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (stored : Stored beforeCaller.checked.native) :
    Stored (SourcePruningEnumerationTerminal.run checkEmpty r n p h first rest waiting
      beforeCaller before incoming incomingScs memos.query).2.1.checked.native := by
  rw [SourcePruningEnumerationTerminal.run]
  by_cases empty : incoming = .empty
  · simpa only [ite_eq_left empty] using stored
  · simp only [ite_eq_right empty]
    cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) with
    | nil =>
        simpa only [prefixObserved] using stored
    | cons prefixEntry prefixTail =>
        cases prefixEntry with
        | error fault =>
            simpa only [prefixObserved] using stored
        | ok prefixResult =>
            rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons second remaining =>
                simpa only [prefixObserved] using stored
            | nil =>
                simp only
                obtain ⟨recordedSame, joinedRealized, winnerPending, recordedPending⟩ :=
                  SourcePruningEnumerationCachedTerminalAdapter.observed_prefix
                    beforeCaller.checked.native.machine.heap before first rest waiting roots
                    paths counts safe bounded pending realized prefixObserved
                have countSame : recorded.length = (first :: rest).length := by
                  rw [recordedSame, List.length_map]
                have foldReservation : Reserved bits seed recorded.length :=
                  reserved.prefix (by rw [countSame]; omega)
                have selected : ∀ source ∈ recorded, PendingOrEliminated joined source :=
                  fun source member => .inl (recordedPending source member)
                have foldStored := SourceCurrentAllocatedNativeStoredFold.fold_native_stored seed formulas solver inventory
                  beforeCaller joined recorded checkEmpty n p h winner memos initial joinedRealized winnerPending
                  selected fits foldReservation known stored
                rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded
                    beforeCaller joined winner memos.query with
                  ⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩
                rw [foldObserved] at foldStored
                change Stored foldCaller.checked.native at foldStored
                cases foldOutcome with
                | error fault =>
                    simpa only [foldObserved] using foldStored
                | ok possible =>
                    cases possible with
                    | none =>
                        simpa only [foldObserved] using foldStored
                    | some foldRaw =>
                        cases foldRaw with
                        | nil =>
                            simpa only [foldObserved] using foldStored
                        | cons firstRow tail =>
                            cases firstRow with
                            | error fault =>
                                simpa only [foldObserved] using foldStored
                            | ok row =>
                                rcases row with ⟨token, folded⟩
                                cases token
                                cases tail with
                                | cons second remaining =>
                                    simpa only [foldObserved] using foldStored
                                | nil =>
                                    simp only
                                    have foldRanges := SourcePruningEnumerationFold.initial_ranges seed
                                      formulas solver inventory beforeCaller joined recorded checkEmpty winner memos
                                      initial joinedRealized winnerPending selected fits foldReservation known
                                    obtain ⟨fuel, lowP, lowH, raw, actualCaller, actualCore, actualQueries,
                                      final, next, stable, post, querySame, finalRealized, shape,
                                      _completed, _eliminated, _length, _forest, _counter, _obligations,
                                      _expansion, _ancestry, _rejection⟩ :=
                                      SourcePruningEnumerationFold.run_complete formulas solver inventory
                                        beforeCaller joined recorded checkEmpty winner memos initial joinedRealized
                                        winnerPending (fun source member => .inr (recordedPending source member)) foldRanges
                                    have actual := stable 0 lowP lowH (Nat.le_refl _) (Nat.le_refl _)
                                    simp only [Nat.add_zero] at actual
                                    obtain ⟨rawSame, callerSame, queriesSame, _outerSame⟩ :=
                                      SourcePruningEnumerationFold.ok_unique checkEmpty actual foldObserved
                                    subst actualCaller
                                    rw [queriesSame] at querySame
                                    have rawSame := Option.some.inj rawSame
                                    have coreSame : actualCore = folded := by
                                      rcases shape with rejected | completed
                                      · rw [rejected] at rawSame
                                        cases rawSame
                                      · have pairSame := Except.ok.inj (List.cons.inj (completed.symm.trans rawSame)).1
                                        exact (Prod.mk.inj pairSame).2
                                    rw [coreSame] at finalRealized
                                    have foldBounds := SourcePruningEnumerationFold.observed_resources seed formulas solver inventory
                                      beforeCaller joined recorded checkEmpty n p h winner memos initial joinedRealized
                                      winnerPending selected fits foldReservation known foldObserved
                                    have incomingStored := SourceCurrentAllocatedNativeStoredIncoming.incoming_run_stored
                                      (advance seed recorded.length).2 checkEmpty r n p h foldCaller folded winner incoming
                                      incomingScs foldQueries post.context.ready finalRealized
                                      (post.effects.keeps.available incoming available) closed foldBounds.1
                                      (reserved recorded.length (by rw [countSame]; omega)) foldStored
                                    rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                                        foldCaller folded winner incoming incomingScs foldQueries with
                                      ⟨incomingOutcome, reachedCaller, reachedQueries, read⟩
                                    rw [incomingObserved] at incomingStored
                                    change Stored reachedCaller.checked.native at incomingStored
                                    cases incomingOutcome with
                                    | error fault =>
                                        simpa only [incomingObserved] using incomingStored
                                    | ok incomingRaw =>
                                        cases incomingRaw <;> simpa only [incomingObserved] using incomingStored

end MicroCFTA.SourceCurrentAllocatedNativeStoredTerminal
