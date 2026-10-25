import MicroCFTA.SourcePruningEnumerationCachedTerminal
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

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

/-- Attach a cache candidate to the exact original terminal observation. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ((Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  if incoming = .empty then
    ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before)
  else
    match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | [.ok ((recorded, winner, moved), joined)] =>
      match SourcePruningEnumerationCachedFold.run checkEmpty nativeFuel p h recorded
          beforeCaller ⟨joined, before.expandable, moved⟩ winner queries with
      | ((foldResult, foldCaller, foldQueries, foldOuter), foldCache) =>
        match foldResult with
        | .error foldFault =>
            ((.error (.inr (.inl foldFault)), foldCaller, foldQueries, foldOuter, moved), none)
        | .ok none => ((.ok none, foldCaller, foldQueries, foldOuter, moved), none)
        | .ok (some foldRaw) =>
          match foldRaw with
          | [] => ((.ok (some []), foldCaller, foldQueries, foldOuter, moved), foldCache)
          | [.ok ((), folded)] =>
            let incomingObserved : ((Except (NativeOutcome ⊕ WorkerOutcome) (Option Raw)) ×
                Caller width × Queries × EnumerationState.State Symbol Constraint) ×
                Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
              match foldCache with
              | none =>
                  (SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
                    foldCaller folded winner incoming incomingScs foldQueries, none)
              | some recovered =>
                  SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty representativeFuel nativeFuel p h
                    indexFuel foldCaller (EnumerationExpandableIndex.frame folded recovered)
                    winner incoming incomingScs foldQueries
            match incomingObserved with
            | ((incomingResult, afterCaller, savedQueries, read), incomingCache) =>
              match incomingResult with
              | .error incomingFault =>
                  ((.error (.inr (.inl incomingFault)), afterCaller, savedQueries, read, moved), none)
              | .ok none => ((.ok none, afterCaller, savedQueries, read, moved), none)
              | .ok (some incomingRaw) =>
                  ((.ok (some (incomingRaw.map fun row => match row with
                    | .error error => .error error
                    | .ok result => .ok (.hole winner, result.2))),
                    afterCaller, savedQueries, read, moved), incomingCache)
          | stoppedRaw =>
              ((.error (.inr (.inr stoppedRaw)), foldCaller, foldQueries, foldOuter, moved), none)
    | prefixRaw => ((.error (.inl prefixRaw), beforeCaller, queries, before.core, before.waiting), none)

/-- Erase the cache candidate at every fixed execution bound. -/
theorem erase
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (run checkEmpty representativeFuel nativeFuel p h indexFuel first rest beforeCaller before
      incoming incomingScs queries).1 =
      SourcePruningEnumerationTerminal.run checkEmpty representativeFuel nativeFuel p h
        first rest before.waiting beforeCaller before.core incoming incomingScs queries := by
  by_cases empty : incoming = .empty
  · simp only [run, SourcePruningEnumerationTerminal.run, ite_eq_left empty]
  · cases prefixResultEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | nil =>
      simp only [run, SourcePruningEnumerationTerminal.run, ite_eq_right empty, prefixResultEq]
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error prefixError =>
        simp only [run, SourcePruningEnumerationTerminal.run, ite_eq_right empty, prefixResultEq]
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
        cases prefixTail with
        | cons prefixNext prefixRest =>
          simp only [run, SourcePruningEnumerationTerminal.run, ite_eq_right empty, prefixResultEq]
        | nil =>
          cases cachedFoldResult : SourcePruningEnumerationCachedFold.run checkEmpty nativeFuel p h
              recorded beforeCaller ⟨joined, before.expandable, moved⟩ winner queries with
          | mk foldObservation foldCache =>
            rcases foldObservation with ⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩
            have foldErased : SourcePruningEnumerationFold.run checkEmpty nativeFuel p h recorded
                beforeCaller joined winner queries = (foldOutcome, foldCaller, foldQueries, foldOuter) := by
              rw [← SourcePruningEnumerationCachedFold.erase checkEmpty nativeFuel p h recorded
                beforeCaller ⟨joined, before.expandable, moved⟩ winner queries, cachedFoldResult]
            simp only [run, SourcePruningEnumerationTerminal.run, ite_eq_right empty,
              prefixResultEq, cachedFoldResult, foldErased]
            cases foldOutcome with
            | error foldFault => rfl
            | ok foldReturned =>
              cases foldReturned with
              | none => rfl
              | some foldRaw =>
                cases foldRaw with
                | nil => rfl
                | cons foldEntry foldTail =>
                  cases foldEntry with
                  | error foldError => rfl
                  | ok foldValue =>
                    rcases foldValue with ⟨foldUnit, folded⟩
                    cases foldUnit
                    cases foldTail with
                    | cons foldNext foldRest => rfl
                    | nil =>
                      cases foldCache with
                      | none =>
                        cases fallbackIncomingResult : SourcePruningEnumerationIncomingNode.run
                            checkEmpty representativeFuel nativeFuel p h foldCaller folded
                            winner incoming incomingScs foldQueries with
                        | mk incomingOutcome incomingObservation =>
                          rcases incomingObservation with ⟨afterCaller, savedQueries, read⟩
                          simp only [fallbackIncomingResult]
                          cases incomingOutcome with
                          | error incomingFault => rfl
                          | ok incomingReturned =>
                            cases incomingReturned with
                            | none => rfl
                            | some incomingRaw => rfl
                      | some recovered =>
                        rw [← SourcePruningEnumerationIncomingCacheAdapter.erase checkEmpty
                          representativeFuel nativeFuel p h indexFuel foldCaller
                          (EnumerationExpandableIndex.frame folded recovered)
                          winner incoming incomingScs foldQueries]
                        cases cachedIncomingResult : SourcePruningEnumerationIncomingCacheAdapter.run
                            checkEmpty representativeFuel nativeFuel p h indexFuel foldCaller
                            (EnumerationExpandableIndex.frame folded recovered)
                            winner incoming incomingScs foldQueries with
                        | mk incomingObservation incomingCache =>
                          rcases incomingObservation with ⟨incomingOutcome, afterCaller, savedQueries, read⟩
                          simp only [cachedIncomingResult]
                          cases incomingOutcome with
                          | error incomingFault => rfl
                          | ok incomingReturned =>
                            cases incomingReturned with
                            | none => rfl
                            | some incomingRaw => rfl

/-- Genuine admitted inputs produce the exact terminal observation and cache. -/
theorem complete
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
      SourcePruningEnumerationFold.Ranges checkEmpty recorded beforeCaller joined winner memos.query ∧
      ∀ (foldFuel P H : Nat) (foldCaller : Caller width)
        (folded : EnumerationState.State Symbol Constraint) (foldQueries : Queries),
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
                final = foldFinal))) := by
  obtain ⟨r, n, p, h, recorded, winner, joined, foldRows, foldCaller, foldQueries,
    foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next,
    prefixRun, recordedSame, winnerMember, movedSame, joinedSame, joinedFlagsSame,
    prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, foldShape, foldPost,
    foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
    foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
    terminalRun, post, querySame, rejectedBranch, completedBranch⟩ :=
    SourcePruningEnumerationCachedTerminal.complete formulas solver inventory beforeCaller before
      checkEmpty first rest incoming incomingScs roots memos initial safe paths counts flags
      bounded pending realized nonempty available closed incomingBounded ranges
  rcases foldShape with rejected | completed
  · subst foldRows
    obtain ⟨rawNil, callerSame, queriesSame, outerSame, _finalSame, _nextSame⟩ := rejectedBranch rfl
    refine ⟨r, n, p, h, 0, recorded, winner, joined, [], foldCaller, foldQueries, foldFinal,
      foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next, folded,
      prefixRun, recordedSame, winnerMember, movedSame, joinedSame, joinedFlagsSame,
      prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun, .inl rfl, foldPost,
      foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage, foldRealized, foldedRoot,
      foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated, foldCompleted,
      terminalRun, post, querySame, ?_,
      foldCounter.trans (congrArg EnumerationState.State.counter joinedSame), foldPaths,
      foldStorage, ?_, foldCounts, ?_, ?_, rejectedBranch, ?_⟩
    · intro extraRepresentative extraNative P H extraIndex enoughP enoughH
      rw [rawNil, callerSame, queriesSame, outerSame]
      simp only [run, ite_eq_right nonempty, prefixRun extraRepresentative,
        ← joinedFlagsSame, cachedFoldRun extraNative P H enoughP enoughH, List.map_nil]
    · simpa only [callerSame] using foldRealized
    · simpa only [callerSame] using foldFlags
    · intro isRejected
      rfl
    · intro isCompleted
      cases isCompleted
  · subst foldRows
    obtain ⟨incomingK, oldNode, oldScs, read, after, replacement, handle, outerRead, reading,
      frame, incomingRun, writePrefix, afterSame, afterStored, afterStorage, afterRealized,
      incomingPost, unfolding, cacheRun, afterCounter, afterRepresentatives, afterPaths,
      afterCounts, writeWaiting, afterFlags, afterExpandable, rawSame, winnerBound,
      replacementAvailable, replacementClosed, encoded, decoded, optional, present⟩ := completedBranch rfl
    obtain ⟨found, lookup, oldStored, _readSame⟩ :=
      (getValue_success r winner folded.core read (.unenumerated oldNode oldScs)).mp (by
        unfold Success
        rw [show ExceptT.run (getValue r winner folded.core) =
          [.ok (.unenumerated oldNode oldScs, read)] from
            by simpa only [Nat.add_zero] using reading 0]
        exact List.mem_singleton_self _)
    have foundTarget : found.representative = winner := by
      obtain ⟨rootSize, rootPath⟩ := foldedRoot
      exact (UnionFind.reaches_unique
        (UnionFind.findRoot_correct r folded.core.representatives winner found lookup).1 rootPath).1
    have readStored : read.values[winner]? = some (.unenumerated oldNode oldScs) := by
      rw [frame.values, ← foundTarget]
      exact oldStored
    have adapted : ∀ extraIndex,
        SourcePruningEnumerationIncomingCacheAdapter.adapt afterCaller.checked.native.machine.heap
          (incomingK + extraIndex) winner incomingScs folded read
          (if replacement = .empty then [] else [.ok ((), after.core)]) = some after := by
      intro extraIndex
      by_cases empty : replacement = .empty
      ·
        have handleZero : handle = 0 := by
          simpa only [empty, encodeNode, Option.some.injEq] using encoded.symm
        simp only [ite_eq_left empty, SourcePruningEnumerationIncomingCacheAdapter.adapt, readStored]
        simpa only [handleZero, afterSame] using cacheRun extraIndex
      · simp only [ite_eq_right empty, SourcePruningEnumerationIncomingCacheAdapter.adapt,
          afterStored, Option.bind_some]
        exact cacheRun extraIndex
    refine ⟨r, n, p, h, incomingK, recorded, winner, joined, [((), folded)], foldCaller,
      foldQueries, foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries,
      final, next, after, prefixRun, recordedSame, winnerMember, movedSame, joinedSame,
      joinedFlagsSame, prefixRoots, prefixCounts, joinedFlags, cachedFoldRun, foldRun,
      .inr rfl, foldPost, foldQuerySame, foldCounter, foldForest, foldPaths, foldStorage,
      foldRealized, foldedRoot, foldPending, foldCounts, foldWaiting, foldFlags, foldEliminated,
      foldCompleted, terminalRun, post, querySame, ?_,
      afterCounter.trans (foldCounter.trans (congrArg EnumerationState.State.counter joinedSame)),
      afterPaths, afterStorage, afterRealized, afterCounts, afterFlags, ?_, rejectedBranch, ?_⟩
    · intro extraRepresentative extraNative P H extraIndex enoughP enoughH
      rw [outerRead, rawSame]
      simp only [run, ite_eq_right nonempty, prefixRun extraRepresentative,
        ← joinedFlagsSame, cachedFoldRun extraNative P H enoughP enoughH,
        List.map_cons, List.map_nil, SourcePruningEnumerationIncomingCacheAdapter.run,
        incomingRun extraRepresentative extraNative P H enoughP enoughH,
        adapted extraIndex, apply_ite]
    · simp
    · intro isCompleted
      exact ⟨incomingK, oldNode, oldScs, read, after, replacement, handle, rfl, outerRead,
        reading, frame, incomingRun, writePrefix, afterSame, afterStored, afterStorage,
        afterRealized, incomingPost, unfolding, cacheRun, afterCounter, afterRepresentatives,
        afterPaths, afterCounts, writeWaiting, afterFlags, afterExpandable, rawSame,
        winnerBound, replacementAvailable, replacementClosed, encoded, decoded, optional, present⟩

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
