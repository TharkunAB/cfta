import MicroCFTA.SourcePruningEnumerationSharedTerminalNeutralLanguage
import MicroCFTA.SourcePruningEnumerationTerminalPrefixUnique

/-!
# Neutral assignment meaning of an actual stable terminal observation

One canonical receipt identifies the actual branch list at common bounds.
The actual prefix receipt fixes the winner used by the incoming constraints.
No equality of full memo records follows from the returned query memo.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- The stable shared terminal observation has the current assignment meaning. -/
theorem stable_neutral_semantics
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checkEmpty : Bool) (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (nonempty : incoming ≠ .empty)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingBounded : ∀ sc ∈ incomingScs, sc.var < before.core.counter)
    (ranges : TerminalRanges checkEmpty first rest beforeCaller before incoming memos.query)
    {r n p h : Nat} {recorded : List Nat} {winner : Nat}
    {moved : EnumerationWaitingIndex.Waiting} {joined : EnumerationState.State Symbol Constraint}
    {raw : List (Except EnumerationState.Error (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))}
    {afterCaller : Caller width} {savedQueries : Queries} {outer : EnumerationState.State Symbol Constraint}
    (prefixObserved : ∀ extra,
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run (r + extra) first rest before.waiting before.core) =
        [.ok ((recorded, winner, moved), joined)])
    (observed : ∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
      SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty (r + extraRepresentative) (n + extraNative) P H
        first rest before.waiting beforeCaller before.core incoming incomingScs memos.query =
        (.ok (some raw), afterCaller, savedQueries, outer, moved)) :
    ∀ (held : Nat), Avoids before.core.representatives held (first :: rest) →
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      (∃ (fragment : Fragments.Fragment Symbol) (output : EnumerationState.State Symbol Constraint),
        Except.ok (fragment, output) ∈ raw ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔
      (Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held before.core) ∧
        ∀ sc ∈ rest, assignment first.var = assignment sc.var) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming (assignment winner) ∧
        ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment winner) sc := by
  obtain ⟨r0, n0, p0, h0, recorded0, winner0, joined0, _foldRows,
    _foldCaller, _foldQueries, _foldFinal, _foldInventory, _folded,
    raw0, caller0, outer0, queries0, _final, _next,
    canonicalPrefix, _recordedSame, _winnerMember, _movedSame, _joinedSame, _joinedFlagsSame,
    _prefixRoots, _prefixCounts, _joinedFlags, _cachedFoldRun, _foldRun, _foldShape, _foldPost,
    _foldQuerySame, _foldCounter, _foldForest, _foldPaths, _foldStorage, _foldRealized, _foldedRoot,
    _foldPending, _foldCounts, _foldWaiting, _foldFlags, _foldEliminated, _foldCompleted,
    _foldedFrame, _foldedSafe, _foldedOrigin,
    canonicalRun, _post, _querySame, _rejectedBranch, _completedBranch, semantic⟩ :=
      terminal_complete_neutral_semantics formulas solver inventory beforeCaller before
        checkEmpty first rest incoming incomingScs roots memos initial safe paths counts flags
        bounded pending realized nonempty available closed incomingBounded ranges
  have actualPrefix : ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting before.core) =
      [.ok ((recorded, winner, moved), joined)] := by
    simpa only [Nat.add_zero] using prefixObserved 0
  have canonicalPrefixObserved : ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r0 first rest before.waiting before.core) =
      [.ok ((recorded0, winner0, joined0.waiting), joined0.core)] := by
    simpa only [Nat.add_zero] using canonicalPrefix 0
  obtain ⟨_recordedEq, winnerSame, _movedEq, _joinedEq⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_unique first rest before.waiting before.core
      actualPrefix canonicalPrefixObserved
  have canonicalObserved :
      SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty (r + r0) (n + n0)
        (max p p0) (max h h0) first rest before.waiting beforeCaller before.core
        incoming incomingScs memos.query =
        (.ok (some raw0), caller0, queries0, outer0, joined0.waiting) := by
    simpa only [Nat.add_comm] using
      canonicalRun r n (max p p0) (max h h0) (Nat.le_max_right p p0) (Nat.le_max_right h h0)
  have actualObserved :=
    observed r0 n0 (max p p0) (max h h0) (Nat.le_max_left p p0) (Nat.le_max_left h h0)
  have same : raw = raw0 ∧ afterCaller = caller0 ∧ savedQueries = queries0 ∧
      outer = outer0 ∧ moved = joined0.waiting := by
    simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] using
      actualObserved.symm.trans canonicalObserved
  obtain ⟨rawSame, callerSame, _queriesSame, _outerSame, _waitingSame⟩ := same
  intro held avoids ambient residualMeaning assignment
  simpa only [rawSame, callerSame, winnerSame] using semantic held avoids ambient residualMeaning assignment

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
