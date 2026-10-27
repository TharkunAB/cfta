import MicroCFTA.SourcePruningEnumerationTerminalNeutralLanguage
import MicroCFTA.SourcePruningEnumerationTerminalPrefixUnique

/-!
# Neutral assignment meaning of an actual stable terminal observation

One canonical receipt identifies the actual branch list at common bounds.
The actual prefix receipt fixes the winner used by the incoming constraints.
No equality of full memo records follows from the returned query memo.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminal
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
variable {EnumGuard : Type} {width : Nat}

/-- The stable actual terminal branches have the canonical assignment meaning at their own winner. -/
theorem stable_neutral_semantics
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before) (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (nonempty : incoming ≠ .empty)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingBounded : ∀ sc ∈ incomingScs, sc.var < before.counter)
    (ranges : ∀ (prefixFuel : Nat) (recorded : List Nat) (winner : Nat)
      (moved : EnumerationWaitingIndex.Waiting) (joined : EnumerationState.State Symbol EnumGuard),
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run prefixFuel first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)] →
      SourcePruningEnumerationFold.Ranges checkEmpty recorded beforeCaller joined winner memos.query ∧
      ∀ (foldFuel P H : Nat) (foldCaller : Caller width)
        (folded : EnumerationState.State Symbol EnumGuard) (foldQueries : Queries),
        SourcePruningEnumerationFold.run checkEmpty foldFuel P H recorded beforeCaller joined winner memos.query =
          (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, folded) →
        match folded.values[winner]? with
        | some (.unenumerated (some oldHandle) _) =>
            match lookupNode foldCaller.checked.native.machine.heap oldHandle with
            | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                foldCaller.checked
            | none => True
        | _ => True)
    {r n p h : Nat} {recorded : List Nat} {winner : Nat}
    {moved : EnumerationWaitingIndex.Waiting} {joined : EnumerationState.State Symbol EnumGuard}
    {raw : List (Except EnumerationState.Error (Fragments.Fragment Symbol × EnumerationState.State Symbol EnumGuard))}
    {afterCaller : Caller width} {savedQueries : Queries} {outer : EnumerationState.State Symbol EnumGuard}
    (prefixObserved : ∀ extra,
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run (r + extra) first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)])
    (observed : ∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
      run checkEmpty (r + extraRepresentative) (n + extraNative) P H first rest waiting
        beforeCaller before incoming incomingScs memos.query =
        (.ok (some raw), afterCaller, savedQueries, outer, moved)) :
    ∀ (held : Nat), Avoids before.representatives held (first :: rest) →
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      (∃ (fragment : Fragments.Fragment Symbol) (output : EnumerationState.State Symbol EnumGuard),
        Except.ok (fragment, output) ∈ raw ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔
      (Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held before) ∧
        ∀ sc ∈ rest, assignment first.var = assignment sc.var) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming (assignment winner) ∧
        ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment winner) sc := by
  obtain ⟨r0, n0, p0, h0, recorded0, winner0, moved0, joined0,
    _foldRaw, _foldCaller, _folded, _foldQueries, _foldFinal, _foldInventory,
    raw0, caller0, outer0, queries0, _final, _next, canonicalPrefix,
    _recordedSame, _winnerMember, _movedSame, _foldRun, _foldShape, _foldPost, _foldQuerySame,
    _foldedStorage, _foldedRealized, _foldedRoot, _foldCounts, canonicalRun, _post, _querySame,
    _rejected, _survived, semantic⟩ :=
      run_complete_neutral_semantics formulas solver inventory beforeCaller before checkEmpty first rest incoming incomingScs
        waiting roots memos initial safe paths counts bounded pending realized nonempty available closed incomingBounded ranges
  have actualPrefix : ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) =
      [.ok ((recorded, winner, moved), joined)] := by
    simpa only [Nat.add_zero] using prefixObserved 0
  have canonicalPrefixObserved : ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r0 first rest waiting before) =
      [.ok ((recorded0, winner0, moved0), joined0)] := by
    simpa only [Nat.add_zero] using canonicalPrefix 0
  obtain ⟨_recordedEq, winnerSame, _movedEq, _joinedEq⟩ :=
    SourcePruningEnumerationTerminalPrefix.run_unique first rest waiting before actualPrefix canonicalPrefixObserved
  have canonicalObserved :
      run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0) first rest waiting
        beforeCaller before incoming incomingScs memos.query =
        (.ok (some raw0), caller0, queries0, outer0, moved0) := by
    simpa only [Nat.add_comm] using
      canonicalRun r n (max p p0) (max h h0) (Nat.le_max_right p p0) (Nat.le_max_right h h0)
  have actualObserved :=
    observed r0 n0 (max p p0) (max h h0) (Nat.le_max_left p p0) (Nat.le_max_left h h0)
  have same : raw = raw0 ∧ afterCaller = caller0 ∧ savedQueries = queries0 ∧ outer = outer0 ∧ moved = moved0 := by
    simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] using
      actualObserved.symm.trans canonicalObserved
  obtain ⟨rawSame, callerSame, _queriesSame, _outerSame, _waitingSame⟩ := same
  intro held avoids ambient residualMeaning assignment
  simpa only [rawSame, callerSame, winnerSame] using semantic held avoids ambient residualMeaning assignment

end MicroCFTA.SourcePruningEnumerationTerminal
