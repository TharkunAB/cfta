import MicroCFTA.SourcePruningEnumerationTerminalObservedResources
import MicroCFTA.SourcePruningEnumerationFoldArity
import MicroCFTA.SourcePruningEnumerationIncomingNodeObservedArity

/-!
# Arity at actual terminal returns

The original fold and incoming query retain their exact caller heaps.
Early returns keep the reached heap even when the enum result is empty.
The theorem keeps every original resource admission.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationCompleteness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed step advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {EnumGuard : Type} {bits : Nat}
local notation "Core" => EnumerationState.State Symbol EnumGuard
local notation "TerminalRaw" => List (Except EnumerationState.Error (Fragments.Fragment Symbol × Core))

/-- The actual outer successful terminal endpoint retains whole native arity. -/
theorem observed_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Core)
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
    (arityHeap : SourcePruningEnumerationArityOrigins.Heap beforeCaller.checked.native.machine.heap)
    {result : Option TerminalRaw} {afterCaller : Caller (bits + 2)}
    {savedQueries : Queries} {outer : Core} {afterWaiting : EnumerationWaitingIndex.Waiting}
    (observed : run checkEmpty r n p h first rest waiting beforeCaller before incoming incomingScs memos.query =
      (.ok result, afterCaller, savedQueries, outer, afterWaiting)) :
    SourcePruningEnumerationArityOrigins.Heap afterCaller.checked.native.machine.heap := by
  rw [run] at observed
  by_cases empty : incoming = .empty
  · simp only [ite_eq_left empty] at observed
    have callerSame := congrArg (fun output => output.2.1) observed
    dsimp only at callerSame
    rw [← callerSame]
    exact arityHeap
  · simp only [ite_eq_right empty] at observed
    cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) with
    | nil =>
        simp only [prefixObserved] at observed
        cases observed
    | cons prefixEntry prefixTail =>
        cases prefixEntry with
        | error fault =>
            simp only [prefixObserved] at observed
            cases observed
        | ok prefixResult =>
            rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons second remaining =>
                simp only [prefixObserved] at observed
                cases observed
            | nil =>
                simp only [prefixObserved] at observed
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
                rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded
                    beforeCaller joined winner memos.query with
                  ⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩
                cases foldOutcome with
                | error fault =>
                    simp only [foldObserved] at observed
                    cases observed
                | ok possible =>
                    have foldBounds := SourcePruningEnumerationFold.observed_resources seed formulas solver inventory
                      beforeCaller joined recorded checkEmpty n p h winner memos initial joinedRealized
                      winnerPending selected fits foldReservation known foldObserved
                    have padded := SourcePruningEnumerationFold.observed_heap seed formulas solver inventory
                      beforeCaller joined recorded checkEmpty n p h winner memos initial joinedRealized
                      winnerPending selected fits foldReservation known arityHeap foldObserved
                    cases possible with
                    | none =>
                        simp only [foldObserved] at observed
                        have callerSame := congrArg (fun output => output.2.1) observed
                        dsimp only at callerSame
                        rw [← callerSame]
                        exact padded
                    | some foldRaw =>
                        cases foldRaw with
                        | nil =>
                            simp only [foldObserved] at observed
                            have callerSame := congrArg (fun output => output.2.1) observed
                            dsimp only at callerSame
                            rw [← callerSame]
                            exact padded
                        | cons firstRow tail =>
                            cases firstRow with
                            | error fault =>
                                simp only [foldObserved] at observed
                                cases observed
                            | ok row =>
                                rcases row with ⟨token, folded⟩
                                cases token
                                cases tail with
                                | cons second remaining =>
                                    simp only [foldObserved] at observed
                                    cases observed
                                | nil =>
                                    simp only [foldObserved] at observed
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
                                    rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                                        foldCaller folded winner incoming incomingScs foldQueries with
                                      ⟨incomingOutcome, reachedCaller, reachedQueries, read⟩
                                    cases incomingOutcome with
                                    | error fault =>
                                        simp only [incomingObserved] at observed
                                        cases observed
                                    | ok incomingRaw =>
                                        have incomingBounds := SourcePruningEnumerationIncomingNode.observed_heap
                                          (advance seed recorded.length).1 (advance seed recorded.length).2
                                          formulas solver next foldCaller folded checkEmpty r n p h winner incoming
                                          incomingScs final post.context finalRealized
                                          (post.effects.keeps.available incoming available) closed foldBounds.1
                                          (reserved recorded.length (by rw [countSame]; omega)) foldBounds.2 padded
                                          (by simpa only [querySame] using incomingObserved)
                                        cases incomingRaw <;> simp only [incomingObserved] at observed <;>
                                          have callerSame := congrArg (fun output => output.2.1) observed <;>
                                          dsimp only at callerSame <;>
                                          rw [← callerSame] <;> exact incomingBounds

end MicroCFTA.SourcePruningEnumerationTerminal
