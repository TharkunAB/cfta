import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
import MicroCFTA.SourcePruningEnumerationTerminalStableLanguage

/-!
# Assignment language of the cached terminal adapter

The original completion producer runs once. Every receipt remains available.
The semantic clause uses the actual raw rows and reached native heap.
The attached cache remains separate from branch acceptance on rejection.
-/

namespace MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
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
local notation "Raw" => List (Except EnumerationState.Error
  (Unit × EnumerationState.State Symbol Constraint))
local notation "PrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationState.State Symbol Constraint))
local notation "FoldRaw" => Raw
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
variable {width : Nat}
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome width Node
local notation "WorkerOutcome" => SourceCurrentAllocatedConjunctionWorker.Outcome width
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- Retain every cache receipt and interpret only actual terminal branch rows. -/
theorem complete_semantics
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
    (ranges : Ranges checkEmpty first rest beforeCaller before incoming memos.query) :
    ∃ (r n p h k : Nat) (recorded : List Nat) (winner : Nat)
      (joined : EnumerationExpandableIndex.Cached Symbol Constraint)
      (foldRows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (foldCaller : Caller width) (foldQueries : Queries) (foldFinal : Memos) (foldInventory : Inventory)
      (folded : EnumerationExpandableIndex.Cached Symbol Constraint)
      (raw : TerminalRaw) (afterCaller : Caller width) (outer : EnumerationState.State Symbol Constraint)
      (savedQueries : Queries) (final : Memos) (next : Inventory)
      (resultCache : EnumerationExpandableIndex.Cached Symbol Constraint),
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
        SourcePruningEnumerationCachedFold.run checkEmpty (n + extra) P H recorded
          beforeCaller joined winner memos.query =
          ((.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
            foldCaller, foldQueries, folded.core), some folded)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationFold.run checkEmpty (n + extra) P H recorded
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
        SourcePruningEnumerationTerminal.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
          first rest before.waiting beforeCaller before.core incoming incomingScs memos.query =
          (.ok (some raw), afterCaller, savedQueries, outer, joined.waiting)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        run checkEmpty (r + extraRepresentative) (n + extraNative) P H (k + extraIndex)
          first rest beforeCaller before incoming incomingScs memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, joined.waiting), some resultCache)) ∧
      resultCache.core.counter = before.core.counter ∧
      Roots resultCache.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      StorageValid resultCache.core ∧ PendingRealized afterCaller.checked.native.machine.heap resultCache.core ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        resultCache.core.values resultCache.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((resultCache.core.values[slot]?).getD .eliminated) = some (resultCache.expandable slot)) ∧
      (∀ (slot : Nat), slot ∉ recorded → resultCache.core.values[slot]? = before.core.values[slot]?) ∧
      (raw ≠ [] → Safe resultCache.core) ∧
      (∀ (held : Nat), IsRoot before.core.representatives held →
        Avoids before.core.representatives held (first :: rest) →
        EnumerationDriver.Protected held before.core resultCache.core) ∧
      (∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        resultCache.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment)) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed incomingScs →
        EnumerationReferences.ReferencesAllowed allowed resultCache.core) ∧
      (foldRows = [] → resultCache = folded) ∧
      (foldRows = [] → raw = [] ∧ afterCaller = foldCaller ∧ savedQueries = foldQueries ∧
        outer = folded.core ∧ final = foldFinal ∧ next = foldInventory) ∧
      (foldRows = [((), folded)] →
        ∃ (incomingK : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
          (read : EnumerationState.State Symbol Constraint)
          (after : EnumerationExpandableIndex.Cached Symbol Constraint) (replacement : Node) (handle : Nat),
          after = resultCache ∧ outer = read ∧
          (∀ extra, ExceptT.run (getValue (r + extra) winner folded.core) =
            [.ok (.unenumerated oldNode oldScs, read)]) ∧
          EnumerationCompressionFrame.Frame folded.core read ∧
          (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationIncomingNode.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
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
            (incomingK + extra) winner (.unenumerated (some handle) (incomingScs ++ oldScs)) incomingScs []
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
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        (∃ (fragment : Fragments.Fragment Symbol) (output : EnumerationState.State Symbol Constraint),
          Except.ok (fragment, output) ∈ raw ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) ↔
        (Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
          ∀ sc ∈ rest, assignment first.var = assignment sc.var) ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient incoming (assignment winner) ∧
          ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment winner) sc := by
  obtain ⟨
    r, n, p, h, k, recorded, winner, joined, foldRows, foldCaller, foldQueries, foldFinal, foldInventory,
    folded, raw, afterCaller, outer, savedQueries, final, next, resultCache, prefixRun, recordedSame,
    winnerMember, movedSame, joinedSame, joinedFlagsSame, prefixRoots, prefixCounts, joinedFlags,
    cachedFoldRun, foldRun, foldShape, foldPost, foldQuerySame, foldCounter, foldForest, foldPaths,
    foldStorage, foldRealized, foldedRoot, foldPending, foldCounts, foldWaiting, foldFlags,
    foldEliminated, foldCompleted, foldedFrame, foldedSafe, foldedOrigin, terminalRun, post, querySame,
    adapterRun, resultCounter, resultPaths, resultStorage, resultRealized, resultCounts, resultFlags,
    resultFrame, resultSafe, resultProtected, resultOrigin, resultAllowed, rejectedCache, rejectedBranch,
    completedBranch⟩ :=
      complete formulas solver inventory beforeCaller before checkEmpty first rest incoming incomingScs roots memos
        initial safe paths counts flags bounded pending realized nonempty available closed incomingBounded ranges
  refine ⟨
    r, n, p, h, k, recorded, winner, joined, foldRows, foldCaller, foldQueries, foldFinal, foldInventory,
    folded, raw, afterCaller, outer, savedQueries, final, next, resultCache, prefixRun, recordedSame,
    winnerMember, movedSame, joinedSame, joinedFlagsSame, prefixRoots, prefixCounts, joinedFlags,
    cachedFoldRun, foldRun, foldShape, foldPost, foldQuerySame, foldCounter, foldForest, foldPaths,
    foldStorage, foldRealized, foldedRoot, foldPending, foldCounts, foldWaiting, foldFlags,
    foldEliminated, foldCompleted, foldedFrame, foldedSafe, foldedOrigin, terminalRun, post, querySame,
    adapterRun, resultCounter, resultPaths, resultStorage, resultRealized, resultCounts, resultFlags,
    resultFrame, resultSafe, resultProtected, resultOrigin, resultAllowed, rejectedCache, rejectedBranch,
    completedBranch, ?_⟩
  exact SourcePruningEnumerationTerminal.stable_semantics
    formulas solver inventory beforeCaller before.core checkEmpty first rest incoming incomingScs
    before.waiting roots memos initial safe paths counts bounded pending realized nonempty available closed
    incomingBounded ranges prefixRun terminalRun

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
