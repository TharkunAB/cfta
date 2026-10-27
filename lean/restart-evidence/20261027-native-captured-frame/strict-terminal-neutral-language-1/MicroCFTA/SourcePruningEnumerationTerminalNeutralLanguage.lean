import MicroCFTA.SourcePruningEnumerationTerminal
import MicroCFTA.SourcePruningEnumerationTerminalPrefixObservedLanguage
import MicroCFTA.SourcePruningEnumerationFoldLanguage
import MicroCFTA.SourcePruningEnumerationFoldUnique
import MicroCFTA.SourcePruningEnumerationIncomingStableNeutral
import MicroCFTA.SourcePruningEnumerationTerminalPrefixNeutral
import MicroCFTA.SourcePruningEnumerationFoldObservedNeutral

/-!
# Neutral assignment language of the complete actual terminal arm

The original terminal producer runs once and retains every receipt.
The actual prefix adds its union equations. The full fold retains exactly
those assignments. The incoming step adds its node and suspended constraints.
Empty rejection retains its actual native endpoint and has no accepted branch.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
local notation "PrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationState.State Symbol EnumGuard))
local notation "FoldRaw" => List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol EnumGuard))
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome width Node
local notation "WorkerOutcome" => SourceCurrentAllocatedConjunctionWorker.Outcome width

attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- The actual terminal arm accepts exactly the original assignments with its requested restrictions. -/
theorem run_complete_neutral_semantics
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
        | _ => True) :
    ∃ (r n p h : Nat) (recorded : List Nat) (winner : Nat)
      (moved : EnumerationWaitingIndex.Waiting) (joined : EnumerationState.State Symbol EnumGuard)
      (foldRaw : FoldRaw) (foldCaller : Caller width) (folded : EnumerationState.State Symbol EnumGuard)
      (foldQueries : Queries) (foldFinal : Memos) (foldInventory : Inventory)
      (raw : TerminalRaw) (afterCaller : Caller width) (outer : EnumerationState.State Symbol EnumGuard)
      (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run (r + extra) first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)]) ∧
      recorded = (first :: rest).map (fun sc => roots sc.var) ∧ winner ∈ recorded ∧
      moved = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))) waiting ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationFold.run checkEmpty (n + extra) P H recorded beforeCaller joined winner memos.query =
          (.ok (some foldRaw), foldCaller, foldQueries, folded)) ∧
      (foldRaw = [] ∨ foldRaw = [.ok ((), folded)]) ∧
      Post formulas solver foldInventory beforeCaller foldCaller foldFinal ∧ foldFinal.query = foldQueries ∧
      StorageValid folded ∧ PendingRealized foldCaller.checked.native.machine.heap folded ∧
      IsRoot folded.representatives winner ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        folded.values moved ∧
      (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
        run checkEmpty (r + extraRepresentative) (n + extraNative) P H first rest waiting
          beforeCaller before incoming incomingScs memos.query =
          (.ok (some raw), afterCaller, savedQueries, outer, moved)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      (foldRaw = [] → raw = [] ∧ afterCaller = foldCaller ∧ savedQueries = foldQueries ∧
        outer = folded ∧ final = foldFinal ∧ next = foldInventory) ∧
      (foldRaw = [.ok ((), folded)] →
        ∃ (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
          (read afterWrite : EnumerationState.State Symbol EnumGuard) (replacement : Node) (handle : Nat),
          outer = read ∧
          (∀ extra, ExceptT.run (getValue (r + extra) winner folded) =
            [.ok (.unenumerated oldNode oldScs, read)]) ∧
          EnumerationCompressionFrame.Frame folded read ∧
          (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationIncomingNode.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
              foldCaller folded winner incoming incomingScs foldQueries =
              (.ok (some (if replacement = .empty then [] else [.ok ((), afterWrite)])),
                afterCaller, savedQueries, read)) ∧
          ExceptT.run ((do
            setValue winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            inheritAncestry winner) read) = [.ok ((), afterWrite)] ∧
          afterWrite.values[winner]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
          StorageValid afterWrite ∧ PendingRealized afterCaller.checked.native.machine.heap afterWrite ∧
          EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
            afterWrite.values
            (EnumerationCanonicalWaiting.count (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
              1 incomingScs moved) ∧
          raw = (if replacement = .empty then [] else [.ok (.hole winner, afterWrite)]) ∧
          FragmentBound afterWrite.counter (.hole winner : Fragments.Fragment Symbol) ∧
          Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
          encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
          (oldNode = none → replacement = incoming ∧ afterCaller = foldCaller ∧
            savedQueries = foldQueries ∧ final = foldFinal ∧ next = foldInventory) ∧
          (∀ oldHandle, oldNode = some oldHandle →
            ∃ (old query : Node) (queried : SourceEqualityNativeDemand.State width),
              lookupNode foldCaller.checked.native.machine.heap oldHandle = some old ∧
              next.source = foldCaller.checked.native.machine.heap ∧
              next.roots = foldInventory.roots ++ [incoming, old] ∧
              SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old
                foldCaller.checked query queried foldFinal ∧
              (∀ ambient term,
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term))) ∧
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
  obtain ⟨r, n, p, h, recorded, winner, moved, joined, foldRaw, foldCaller, folded, foldQueries,
    foldFinal, foldInventory, raw, afterCaller, outer, savedQueries, final, next, prefixRun,
    recordedSame, winnerMember, movedSame, foldRun, foldShape, foldPost, foldQuerySame,
    foldedStorage, foldedRealized, foldedRoot, foldCounts, terminalRun, post, querySame,
    rejected, survived⟩ :=
    run_complete formulas solver inventory beforeCaller before checkEmpty first rest incoming incomingScs
      waiting roots memos initial safe paths counts bounded pending realized nonempty available closed incomingBounded ranges
  refine ⟨r, n, p, h, recorded, winner, moved, joined, foldRaw, foldCaller, folded, foldQueries,
    foldFinal, foldInventory, raw, afterCaller, outer, savedQueries, final, next, prefixRun,
    recordedSame, winnerMember, movedSame, foldRun, foldShape, foldPost, foldQuerySame,
    foldedStorage, foldedRealized, foldedRoot, foldCounts, terminalRun, post, querySame,
    rejected, survived, ?_⟩
  have prefixObserved : ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) =
      [.ok ((recorded, winner, moved), joined)] := by
    simpa only [Nat.add_zero] using prefixRun 0
  obtain ⟨joinedSame, _joinedStorage, joinedRealized, winnerPending, sourcesPending,
    classes, _joinedPaths, _prefixMeaning⟩ := SourcePruningEnumerationTerminalPrefix.observed_semantics
      beforeCaller.checked.native.machine.heap before first rest waiting roots paths counts safe bounded pending
      realized prefixObserved
  have foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded beforeCaller joined winner memos.query =
      (.ok (some foldRaw), foldCaller, foldQueries, folded) := by
    simpa only [Nat.add_zero] using foldRun 0 p h (Nat.le_refl _) (Nat.le_refl _)
  have foldRanges := (ranges r recorded winner moved joined prefixObserved).1
  obtain ⟨foldFuel, minimumP, minimumH, canonicalRaw, canonicalCaller, canonicalCore, canonicalQueries,
    _canonicalMemos, _canonicalInventory, stableFold, _canonicalPost, _canonicalQuery, _canonicalRealized,
    _canonicalShape, canonicalComplete, _canonicalEliminated, _canonicalLength, _canonicalForest,
    canonicalCounter, _canonicalObligations, _canonicalExpansion, _canonicalAncestry, _canonicalRejected,
    _foldMeaning⟩ := SourcePruningEnumerationFold.run_complete_semantics formulas solver inventory beforeCaller joined
      recorded checkEmpty winner memos initial joinedRealized winnerPending
      (fun source member => .inr (sourcesPending source member)) foldRanges
  have canonicalFold : SourcePruningEnumerationFold.run checkEmpty foldFuel minimumP minimumH recorded
      beforeCaller joined winner memos.query =
      (.ok (some canonicalRaw), canonicalCaller, canonicalQueries, canonicalCore) := by
    simpa only [Nat.add_zero] using stableFold 0 minimumP minimumH (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨rawsSame, callersSame, _queriesSame, coresSame⟩ :=
    SourcePruningEnumerationFold.ok_unique checkEmpty foldObserved canonicalFold
  have rawSame : foldRaw = canonicalRaw := Option.some.inj rawsSame
  rw [← rawSame, ← coresSame] at canonicalComplete
  rw [← coresSame] at canonicalCounter
  intro held avoids
  have sourcesOther : ∀ source ∈ recorded, source ≠ held := by
    intro source member same
    rw [recordedSame] at member
    obtain ⟨sc, present, rootSame⟩ := List.mem_map.mp member
    apply avoids sc present
    obtain ⟨size, path⟩ := paths sc.var
    have equal : roots sc.var = held := rootSame.trans same
    exact UnionFind.sameClass_symm (by simpa only [equal] using UnionFind.sameClass_root path)
  have winnerOther : winner ≠ held := sourcesOther winner winnerMember
  have prefixMeaning := SourcePruningEnumerationTerminalPrefix.neutral_semantics held r first rest waiting
    before joined recorded winner moved safe.1.total
    (by rw [Success, prefixObserved]; exact List.mem_singleton_self _)
  have actualFoldMeaning : ∀ ambient residualMeaning assignment,
      (∃ output : EnumerationState.State Symbol EnumGuard,
        Except.ok ((), output) ∈ foldRaw ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient foldCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held joined) := by
    intro ambient residualMeaning assignment
    exact SourcePruningEnumerationFold.observed_neutral_semantics formulas solver inventory beforeCaller joined
      recorded checkEmpty winner memos initial joinedRealized winnerPending
      (fun source member => .inr (sourcesPending source member)) foldRanges held winnerOther sourcesOther
      foldObserved ambient residualMeaning assignment classes
  intro ambient residualMeaning assignment
  rcases foldShape with foldRejected | foldCompleted
  · have rawEmpty := (rejected foldRejected).1
    rw [rawEmpty]
    constructor
    · rintro ⟨fragment, output, member, _satisfied⟩
      cases member
    · rintro ⟨prior, _incoming, _suspended⟩
      have joinedSatisfied := (prefixMeaning
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment).mpr prior
      obtain ⟨output, member, _satisfied⟩ :=
        (actualFoldMeaning ambient residualMeaning assignment).mpr joinedSatisfied
      rw [foldRejected] at member
      cases member
  · obtain ⟨oldNode, oldScs, read, afterWrite, replacement, handle, _outerRead, _reading, _frame,
      incomingRun, _writing, _stored, _afterStorage, _afterRealized, _afterCounts, rawWritten,
      _fragmentBound, _replacementAvailable, _replacementClosed, _encoded, _decoded,
      _optional, _present⟩ := survived foldCompleted
    have incomingPending := (canonicalComplete foldCompleted).1
    have foldedBounded : ∀ sc ∈ incomingScs, sc.var < folded.counter := by
      intro sc member
      rw [canonicalCounter]
      simpa only [congrArg EnumerationState.State.counter joinedSame] using incomingBounded sc member
    have incomingRanges := (ranges r recorded winner moved joined prefixObserved).2 n p h
      foldCaller folded foldQueries (by simpa only [foldCompleted] using foldObserved)
    have incomingMeaning := SourcePruningEnumerationIncomingNode.stable_neutral_semantics
      formulas solver foldInventory foldCaller folded checkEmpty winner incoming incomingScs foldFinal
      foldPost.context foldedRealized foldedStorage foldedRoot incomingPending
      (foldPost.effects.keeps.available incoming available) closed foldedBounded incomingRanges held winnerOther
      (r := r) (n := n) (p := p) (h := h)
      (raw := if replacement = .empty then [] else [.ok ((), afterWrite)])
      (afterCaller := afterCaller) (savedQueries := savedQueries) (read := read)
      (by
        intro extra extraNative P H enoughP enoughH
        simpa only [foldQuerySame] using incomingRun extra extraNative P H enoughP enoughH)
    have represented :
        (∃ (fragment : Fragments.Fragment Symbol) (output : EnumerationState.State Symbol EnumGuard),
          Except.ok (fragment, output) ∈ raw ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔
        (∃ output : EnumerationState.State Symbol EnumGuard,
          Except.ok ((), output) ∈ (if replacement = .empty then [] else [.ok ((), afterWrite)] : FoldRaw) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) := by
      rw [rawWritten]
      by_cases empty : replacement = .empty <;> simp [empty, and_assoc]
    have foldedMeaning :
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient foldCaller.checked.native.machine.heap) residualMeaning assignment folded ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held joined) := by
      simpa [foldCompleted] using actualFoldMeaning ambient residualMeaning assignment
    exact represented.trans ((incomingMeaning ambient residualMeaning assignment).trans
      (and_congr_left fun _ => foldedMeaning.trans (prefixMeaning
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment)))

end MicroCFTA.SourcePruningEnumerationTerminal
