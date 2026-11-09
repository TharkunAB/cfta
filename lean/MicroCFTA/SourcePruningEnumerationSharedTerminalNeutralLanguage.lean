import MicroCFTA.SourcePruningEnumerationSharedTerminalCompletion
import MicroCFTA.SourcePruningEnumerationTerminalPrefixObservedLanguage
import MicroCFTA.SourcePruningEnumerationSharedIncomingStableNeutral
import MicroCFTA.SourcePruningEnumerationTerminalPrefixNeutral
import MicroCFTA.SourcePruningEnumerationSharedFoldObservedNeutral

/-!
# Neutral assignments through the shared terminal branch

The current terminal receipt supplies the actual prefix, fold and incoming call.
Each semantic statement uses the same returned branch list and native heap.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "FoldRaw" => List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationSharedCachedTerminal.sharedTerminalMonadList


/-- Retain the current terminal receipt and its neutral assignment meaning. -/
theorem terminal_complete_neutral_semantics
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
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (nonempty : incoming ≠ .empty)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingBounded : ∀ sc ∈ incomingScs, sc.var < before.core.counter)
    (ranges : ∀ (prefixFuel : Nat) (recorded : List Nat) (winner : Nat)
      (moved : EnumerationWaitingIndex.Waiting) (joined : EnumerationState.State Symbol Constraint),
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run prefixFuel first rest before.waiting before.core) =
        [.ok ((recorded, winner, moved), joined)] →
      Ranges checkEmpty recorded beforeCaller joined winner memos.query ∧
      ∀ (foldFuel P H : Nat) (foldCaller : Caller width)
        (folded : EnumerationState.State Symbol Constraint) (foldQueries : Queries),
        rawFold checkEmpty foldFuel P H recorded beforeCaller joined winner memos.query =
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
      (joined : EnumerationExpandableIndex.Cached Symbol Constraint)
      (foldRows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (foldCaller : Caller width) (foldQueries : Queries) (foldFinal : Memos) (foldInventory : Inventory)
      (folded : EnumerationExpandableIndex.Cached Symbol Constraint)
      (raw : TerminalRaw) (afterCaller : Caller width) (outer : EnumerationState.State Symbol Constraint)
      (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        (r + extra) first rest before.waiting before.core) =
        [.ok ((recorded, winner, joined.waiting), joined.core)]) ∧
      recorded = (first :: rest).map (fun sc => roots sc.var) ∧ winner ∈ recorded ∧
      joined.waiting = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))) before.waiting ∧
      joined.core = {before.core with representatives := joined.core.representatives} ∧
      joined.expandable = before.expandable ∧
      Roots joined.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        joined.core.values joined.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        beforeCaller.checked.native.machine.heap
        ((joined.core.values[slot]?).getD .eliminated) = some (joined.expandable slot)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        fold checkEmpty (n + extra) P H recorded
          beforeCaller joined winner memos.query =
          ((.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
            foldCaller, foldQueries, folded.core), some folded)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        rawFold checkEmpty (n + extra) P H recorded
          beforeCaller joined.core winner memos.query =
          (.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
            foldCaller, foldQueries, folded.core)) ∧
      (foldRows = [] ∨ foldRows = [((), folded)]) ∧
      Post formulas solver foldInventory beforeCaller foldCaller foldFinal ∧ foldFinal.query = foldQueries ∧
      folded.core.counter = joined.core.counter ∧ folded.core.representatives = joined.core.representatives ∧
      Roots folded.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      StorageValid folded.core ∧ PendingRealized foldCaller.checked.native.machine.heap folded.core ∧
      IsRoot folded.core.representatives winner ∧ PendingAt folded.core winner ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        folded.core.values folded.waiting ∧ folded.waiting = joined.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        foldCaller.checked.native.machine.heap
        ((folded.core.values[slot]?).getD .eliminated) = some (folded.expandable slot)) ∧
      (∀ (slot : Nat), joined.core.values[slot]? = some .eliminated →
        folded.core.values[slot]? = some .eliminated) ∧
      (foldRows = [((), folded)] → ∀ source ∈ recorded, source ≠ winner →
        folded.core.values[source]? = some .eliminated) ∧
      (∀ (slot : Nat), slot ∉ recorded → folded.core.values[slot]? = before.core.values[slot]?) ∧
      (foldRows = [((), folded)] → Safe folded.core) ∧
      (∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        folded.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment)) ∧
      (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty (r + extraRepresentative) (n + extraNative) P H
          first rest before.waiting beforeCaller before.core incoming incomingScs memos.query =
          (.ok (some raw), afterCaller, savedQueries, outer, joined.waiting)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      (foldRows = [] → raw = [] ∧ afterCaller = foldCaller ∧ savedQueries = foldQueries ∧
        outer = folded.core ∧ final = foldFinal ∧ next = foldInventory) ∧
      (foldRows = [((), folded)] →
        ∃ (k : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
          (read : EnumerationState.State Symbol Constraint)
          (after : EnumerationExpandableIndex.Cached Symbol Constraint) (replacement : Node) (handle : Nat),
          outer = read ∧
          (∀ extra, ExceptT.run (getValue (r + extra) winner folded.core) =
            [.ok (.unenumerated oldNode oldScs, read)]) ∧
          EnumerationCompressionFrame.Frame folded.core read ∧
          (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationSharedIncomingNode.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
              foldCaller folded.core winner incoming incomingScs foldQueries =
              (.ok (some (if replacement = .empty then [] else [.ok ((), after.core)])),
                afterCaller, savedQueries, read)) ∧
          ExceptT.run ((do
            setValue winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            inheritAncestry winner) read) = [.ok ((), after.core)] ∧
          after.core = {read with
            values := read.values.set winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            recursionAncestry := fun other => if other = winner then
              (read.expansionAncestry ++ read.recursionAncestry winner).eraseDups else read.recursionAncestry other} ∧
          after.core.values[winner]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
          StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
          Post formulas solver next foldCaller afterCaller final ∧
          Cache.Extends foldFinal.unfolding final.unfolding ∧
          (∀ extra, (SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
            (k + extra) winner (.unenumerated (some handle) (incomingScs ++ oldScs)) incomingScs []
            (EnumerationExpandableIndex.frame read folded)).map (EnumerationExpandableIndex.frame after.core) = some after) ∧
          after.core.counter = folded.core.counter ∧ after.core.representatives = read.representatives ∧
          Roots after.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
          EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
            after.core.values after.waiting ∧
          after.waiting = EnumerationCanonicalWaiting.count
            (EnumerationCanonicalUnion.mergedRoots roots recorded winner) 1 incomingScs joined.waiting ∧
          (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
            afterCaller.checked.native.machine.heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          after.expandable = (fun slot => if slot = winner then
            !(MergedOrdinaryHeight.recursiveBoundary replacement && (incomingScs ++ oldScs).isEmpty)
            else folded.expandable slot) ∧
          raw = (if replacement = .empty then [] else [.ok (.hole winner, after.core)]) ∧
          FragmentBound after.core.counter (.hole winner : Fragments.Fragment Symbol) ∧
          Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
          encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
          (oldNode = none → replacement = incoming ∧ afterCaller = foldCaller ∧
            savedQueries = foldQueries ∧ final = foldFinal ∧ next = foldInventory) ∧
          (∀ oldHandle, oldNode = some oldHandle →
            ∃ (old query : Node) (queried : Checked width),
              lookupNode foldCaller.checked.native.machine.heap oldHandle = some old ∧
              next.source = foldCaller.checked.native.machine.heap ∧ next.roots = foldInventory.roots ++ [incoming, old] ∧
              SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old foldCaller.checked query queried foldFinal ∧
              (∀ ambient term,
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
              (checkEmpty = false → replacement = query ∧
                afterCaller = SourceCurrentAllocatedPartialState.advance foldCaller queried foldCaller.fourth foldCaller.merge ∧
                final = foldFinal))) ∧
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
  obtain ⟨r, n, p, h, recorded, winner, joined, foldRows, foldCaller, foldQueries,
    foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next,
    prefixRun, recordedSame, winnerMember, movedSame, joinedSame, joinedFlagsSame,
    prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, foldShape, foldPost,
    foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
    foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
    foldedFrame, foldedSafe, foldedOrigin,
    terminalRun, post, querySame, rejectedBranch, completedBranch⟩ :=
    terminal_complete formulas solver inventory beforeCaller before
      checkEmpty first rest incoming incomingScs roots memos initial safe paths counts flags
      bounded pending realized nonempty available closed incomingBounded ranges
  refine ⟨r, n, p, h, recorded, winner, joined, foldRows, foldCaller, foldQueries,
    foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next,
    prefixRun, recordedSame, winnerMember, movedSame, joinedSame, joinedFlagsSame,
    prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, foldShape, foldPost,
    foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
    foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
    foldedFrame, foldedSafe, foldedOrigin,
    terminalRun, post, querySame, rejectedBranch, completedBranch, ?_⟩
  let foldRaw : FoldRaw := foldRows.map (fun row => .ok (row.1, row.2.core))
  have prefixObserved : ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting before.core) =
      [.ok ((recorded, winner, joined.waiting), joined.core)] := by
    simpa only [Nat.add_zero] using prefixRun 0
  obtain ⟨prefixSame, _joinedStorage, joinedRealized, winnerPending, sourcesPending,
    classes, _joinedPaths, _prefixMeaning⟩ := SourcePruningEnumerationTerminalPrefix.observed_semantics
      beforeCaller.checked.native.machine.heap before.core first rest before.waiting roots paths counts safe bounded pending
      realized prefixObserved
  have foldObserved : rawFold checkEmpty n p h recorded beforeCaller joined.core winner memos.query =
      (.ok (some foldRaw), foldCaller, foldQueries, folded.core) := by
    simpa only [Nat.add_zero] using foldRun 0 p h (Nat.le_refl _) (Nat.le_refl _)
  have foldRanges := (ranges r recorded winner joined.waiting joined.core prefixObserved).1
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
  have prefixMeaning := SourcePruningEnumerationTerminalPrefix.neutral_semantics held r first rest before.waiting
    before.core joined.core recorded winner joined.waiting safe.1.total
    (by rw [Success, prefixObserved]; exact List.mem_singleton_self _)
  have actualFoldMeaning : ∀ ambient residualMeaning assignment,
      (∃ output : EnumerationState.State Symbol Constraint,
        Except.ok ((), output) ∈ foldRaw ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient foldCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held joined.core) := by
    intro ambient residualMeaning assignment
    exact observed_neutral_semantics formulas solver inventory beforeCaller joined.core
      recorded checkEmpty winner memos initial joinedRealized winnerPending
      (fun source member => .inr (sourcesPending source member)) foldRanges held winnerOther sourcesOther
      foldObserved ambient residualMeaning assignment classes
  intro ambient residualMeaning assignment
  rcases foldShape with foldRejected | foldCompleted
  · have rawEmpty := (rejectedBranch foldRejected).1
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
      simp only [foldRaw, foldRejected, List.map_nil, List.not_mem_nil] at member
  · obtain ⟨_k, oldNode, oldScs, read, afterWrite, replacement, handle,
      _outerRead, _reading, _frame, incomingRun, _writing, _afterSame,
      _stored, _afterStorage, _afterRealized, _incomingPost, _unfolding,
      _cacheRun, _afterCounter, _afterRepresentatives, _afterPaths, _afterCounts,
      _afterWaiting, _afterFlags, _afterExpandable, rawWritten, _fragmentBound,
      _replacementAvailable, _replacementClosed, _encoded, _decoded, _optional, _present⟩ :=
        completedBranch foldCompleted
    have completedRaw : foldRaw = [.ok ((), folded.core)] := by
      simp only [foldRaw, foldCompleted, List.map_cons, List.map_nil]
    have incomingPending := foldPending
    have foldedBounded : ∀ sc ∈ incomingScs, sc.var < folded.core.counter := by
      intro sc member
      rw [foldCounter]
      simpa only [congrArg EnumerationState.State.counter joinedSame] using incomingBounded sc member
    have incomingRanges := (ranges r recorded winner joined.waiting joined.core prefixObserved).2 n p h
      foldCaller folded.core foldQueries (by simpa only [completedRaw] using foldObserved)
    have incomingMeaning := SourcePruningEnumerationSharedIncomingNode.stable_neutral_semantics
      formulas solver foldInventory foldCaller folded.core checkEmpty winner incoming incomingScs foldFinal
      foldPost.context foldRealized foldStorage foldedRoot incomingPending
      (foldPost.effects.keeps.available incoming available) closed foldedBounded incomingRanges held winnerOther
      (r := r) (n := n) (p := p) (h := h)
      (raw := if replacement = .empty then [] else [.ok ((), afterWrite.core)])
      (afterCaller := afterCaller) (savedQueries := savedQueries) (read := read)
      (by
        intro extra extraNative P H enoughP enoughH
        simpa only [foldQuerySame] using incomingRun extra extraNative P H enoughP enoughH)
    have represented :
        (∃ (fragment : Fragments.Fragment Symbol) (output : EnumerationState.State Symbol Constraint),
          Except.ok (fragment, output) ∈ raw ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔
        (∃ output : EnumerationState.State Symbol Constraint,
          Except.ok ((), output) ∈ (if replacement = .empty then [] else [.ok ((), afterWrite.core)] : FoldRaw) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) := by
      rw [rawWritten]
      by_cases empty : replacement = .empty <;> simp [empty, and_assoc]
    have foldedMeaning :
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient foldCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held folded.core) ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held joined.core) := by
      simpa [completedRaw] using actualFoldMeaning ambient residualMeaning assignment
    exact represented.trans ((incomingMeaning ambient residualMeaning assignment).trans
      (and_congr_left fun _ => foldedMeaning.trans (prefixMeaning
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment)))

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
