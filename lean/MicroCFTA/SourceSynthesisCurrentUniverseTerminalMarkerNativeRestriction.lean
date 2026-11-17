import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourcePruningEnumerationSharedChildObservedResources
import MicroCFTA.SourcePruningEnumerationSharedChildStableNeutral
import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets
import MicroCFTA.SourcePruningEnumerationSharedIncomingBucketHistory

namespace MicroCFTA.SourceSynthesisCurrentUniverseTerminalMarkerNativeRestriction
open Cache Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDependencies EnumerationCompleteness
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourcePruningEnumerationObservation
open SourcePruningEnumerationSharedSelectedContinuations
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {bits : Nat}
set_option autoImplicit false


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem original_universe_terminal_marker_native_restriction
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary)) :
    ∃ (bodyEntry : Interned NodeKey) (marker : Node) (markerEntry : Interned NodeKey)
        (markerRow arrow : Edge) (rows : List Edge),
      body = .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] ∧
      marker = .node markerEntry [markerRow] 0 [] ∧ markerRow.children = [] ∧
      markerRow.entry.key = ⟨literal "(->)", [], SourceSynthesisGeneralizeSyntax.top⟩ ∧
      arrow.children = [marker, .reference (.interned entry.identity), .reference (.interned entry.identity)] ∧
      arrow ∈ canonicalEdges (arrow :: rows) ∧
      ∀ (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
        (solver : SourceGuards.Entailment FullSyntax.Formula)
        (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached)
        (checkEmpty : Bool) (bucket : List Suspended) (roots : Nat → Nat) (memos : Memos),
        Grows sourceHeap caller.checked.native.machine.heap →
        Context formulas solver inventory caller memos →
        Safe before.core → Roots before.core.representatives roots →
        EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting →
        (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
          ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) →
        PendingRealized caller.checked.native.machine.heap before.core →
        (∀ sc ∈ bucket, sc.var < before.core.counter) → InputsPending before.core bucket →
        Fits seed.2 caller.checked → Reserved bits seed (bucket.length + 1) →
        SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
        ∀ (held : Nat), held < before.core.counter → Avoids before.core.representatives held bucket →
        ∀ (r n p h k : Nat) (fragment : Fragment) (reached : Caller (bits + 2))
          (saved : Queries) (read returned : Core) (waiting : EnumerationWaitingIndex.Waiting) (after : Cached),
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true →
          ChildDispatch.run checkEmpty r n p h k bucket marker caller before memos.query =
            ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after) →
          ∃ (winner owner size handle : Nat) (storedBucket : List Suspended) (replacement : Node),
            after.core = returned ∧ fragment = .hole winner ∧
            UnionFind.Reaches returned.representatives winner owner size ∧
            returned.values[owner]? = some (.unenumerated (some handle) storedBucket) ∧
            SourcePruningEnumerationNodes.lookupNode reached.checked.native.machine.heap handle = some replacement ∧
            Available reached.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
            (∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
              UnionFind.SameClass returned.representatives winner sc.var) ∧
            (∀ (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol),
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                ambient replacement term → term = .node (literal "(->)") []) ∧
            ∀ (ambient : InternedGuardedLanguage.Env Symbol)
              (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient reached.checked.native.machine.heap) residualMeaning assignment returned →
                assignment winner = .node (literal "(->)") []
 := by
  /- Note [One observed Marker native domain]
  The actual singleton is retained at its five original supplied fuels.
  Stable completed runs compare receipts at common proof bounds only.
  The raw row, root path, store and lookup identify the same replacement.
  Its native restriction uses the intersection receipt without Satisfies.
  This result does not prove native inhabitance or class consistency.
  -/
  have nullaryMeaning
      (nativeEntry : Interned NodeKey) (row : Edge) (leaf : row.children = [])
      (symbol : row.entry.key.symbol = literal "(->)")
      (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
      (term : Term Symbol)
      (admitted : InternedGuardedLanguage.meaning holds ambient (.node nativeEntry [row] 0 []) term) :
      term = .node (literal "(->)") [] := by
    rw [InternedGuardedLanguage.meaning] at admitted
    obtain ⟨⟨selected, member⟩, checked⟩ := admitted
    have same : selected = row := List.mem_singleton.mp member
    subst selected
    cases row with
    | mk edge children =>
        change children = [] at leaf
        subst children
        change edge.key.symbol = literal "(->)" at symbol
        rw [InternedGuardedLanguage.edgeMeaning] at checked
        obtain ⟨terms, head, forest, _guard⟩ := checked
        cases terms with
        | nil => simpa only [symbol] using head
        | cons first rest => simp only [InternedGuardedLanguage.forest] at forest
  obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, markerRead, arrowChildren, _arrowKey,
      _aligned, markerClosed, sourceAvailable, _kinds, retained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  obtain ⟨markerEntry, markerRow, markerEq, markerChildren, markerKey⟩ := markerRead
  refine ⟨bodyEntry, marker, markerEntry, markerRow, arrow, rows,
    bodyEq, markerEq, markerChildren, markerKey, arrowChildren, retained, ?_⟩
  intro seed formulas solver inventory caller before checkEmpty bucket roots memos
    sourceGrowth initial safe paths counts flags realized bounded pending fits reserved known
    held heldBound heldAvoids r n p h k fragment reached saved read returned waiting after terminal observed
  have currentFacts : Facts caller.checked.native.machine.heap :=
    initial.ready.semantic.ready.semantic.1.normal.facts
  have markerStored : sourceHeap.nodeRecords markerEntry.key = some marker :=
    sourceAvailable.resident markerEntry (by rw [markerEq]; rfl)
  have available : Available caller.checked.native.machine.heap marker :=
    currentFacts.cached.nodes markerEntry.key marker
      (sourceGrowth.nodeRecords markerEntry.key marker markerStored)
  have coreSame : after.core = returned :=
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.singleton_core checkEmpty r n p h k bucket marker
      caller reached before after memos.query saved fragment returned read waiting observed
  obtain ⟨final, next, afterRoots, resource⟩ :=
    ChildDispatch.observed_complete_with_fragments_resources seed formulas solver inventory caller before
      checkEmpty bucket marker roots memos initial safe paths counts flags realized bounded pending
      available markerClosed fits reserved known r n p h k [.ok (fragment, returned)] reached after
      saved read waiting observed (.inr ⟨fragment, returned, rfl⟩)
  obtain ⟨stable, _post, _querySame, _counter, _pathsAfter, _storageAfter, realizedAfter,
      _countsAfter, _flagsAfter, _origins, _protected, _references, _pendingReferences,
      _fragmentResources, _fitsAfter, _knownAfter⟩ := resource
  have ranges := ChildDispatch.initial_ranges seed formulas solver inventory caller before
    checkEmpty bucket marker roots memos initial safe paths counts bounded pending realized available
    markerClosed fits reserved known
  have semantic := ChildDispatch.stable_neutral_semantics formulas solver inventory caller before
    checkEmpty bucket marker roots memos initial safe paths counts flags realized bounded pending
    available markerClosed ranges stable held heldBound heldAvoids
  obtain ⟨first, rest, descendants, recorded, winner, joined, foldCaller, foldQueries, folded, foldOuter,
      partitioned, _prefix, _foldedCall, _foldEndpoint, incomingCall, _recordedSame,
      _joinedValues, hole, _foldForest, _readForest, aliases⟩ :=
    ChildDispatch.terminal_singleton_final_raw_target_incidence checkEmpty r n p h k bucket marker
      caller before memos.query terminal fragment reached saved read returned waiting (some after) roots paths observed
  obtain ⟨found, oldNode, oldScs, handle, lookup, _oldStored, readSame, written, installed, _ancestry⟩ :=
    SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history checkEmpty r n p h
      foldCaller folded winner marker descendants foldQueries returned reached saved read incomingCall
  have rootPath := UnionFind.findRoot_correct r folded.representatives winner found lookup
  have actualPath : UnionFind.Reaches returned.representatives winner found.representative found.size := by
    simpa only [written, readSame] using rootPath.2 rootPath.1
  have returnedRealized : PendingRealized reached.checked.native.machine.heap returned := by
    rw [← coreSame]
    exact realizedAfter
  obtain ⟨replacement, decoded, replacementAvailable, replacementClosed⟩ :=
    returnedRealized found.representative handle (descendants ++ oldScs) installed
  have nativeRestriction : ∀ (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol),
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient replacement term →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient marker term := by
    have nonempty : marker ≠ .empty := by
      rw [markerEq]
      intro impossible
      cases impossible
    have terminalRows : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
      simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
    have belowRows : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) = descendants := by
      simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
    have activeSubset : first :: rest ⊆ bucket := by
      intro sc member
      rw [← terminalRows] at member
      exact (List.mem_filter.mp member).1
    have belowSubset : descendants ⊆ bucket := by
      intro sc member
      rw [← belowRows] at member
      exact (List.mem_filter.mp member).1
    have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
      fun sc member => bounded sc (activeSubset member)
    have activePending : InputsPending before.core (first :: rest) := by
      intro slot expanded present sc member
      exact pending slot expanded present sc (activeSubset member)
    obtain ⟨r0, n0, p0, h0, k0, canonicalRecorded, canonicalWinner, canonicalJoined,
        canonicalFoldRows, _canonicalFoldCaller, _canonicalFoldQueries, _canonicalFoldFinal,
        _canonicalFoldInventory, canonicalFolded, canonicalRaw, canonicalCaller,
        _canonicalOuter, _canonicalQueries, _canonicalFinal, _canonicalNext,
        _canonicalCache, _prefixRun, _canonicalRecordedSame, _winnerMember, _movedSame,
        _joinedSame, _joinedFlagsSame, _prefixRoots, _prefixCounts, _joinedFlags,
        _cachedFoldRun, _foldRun, foldShape, _foldPost, _foldQuerySame, _foldCounter,
        _foldForest, _foldPaths, _foldStorage, _foldRealized, foldedRoot, _foldPending,
        _foldCounts, _foldWaiting, _foldFlags, _foldEliminated, _foldCompleted,
        _foldedFrame, _foldedSafe, _foldedOrigin, _terminalRun, _canonicalPost,
        _canonicalQuerySame, canonicalRun, _resultCounter, _resultPaths, _resultStorage,
        _resultRealized, _resultCounts, _resultFlags, _resultFrame, _resultSafe,
        _resultProtected, _resultOrigin, _resultAllowed, _rejectedCache, rejectedBranch,
        completedBranch, _canonicalSemantic⟩ :=
      SourcePruningEnumerationSharedCachedTerminal.complete_neutral_semantics formulas solver inventory
        caller before checkEmpty first rest marker descendants roots memos initial safe paths counts flags
        activeBounded activePending realized nonempty available markerClosed
        (fun sc member => bounded sc (belowSubset member))
        (ranges nonempty first rest descendants partitioned)
    have canonicalObserved :
        ChildDispatch.run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0) (k + k0)
          bucket marker caller before memos.query =
          ((.ok (some canonicalRaw), canonicalCaller, _canonicalQueries, _canonicalOuter,
            canonicalJoined.waiting), some _canonicalCache) := by
      rw [ChildDispatch.terminal checkEmpty _ _ _ _ _ bucket marker caller before memos.query
        first rest descendants partitioned]
      simpa only [Nat.add_comm] using canonicalRun r n (max p p0) (max h h0) k
        (Nat.le_max_right p p0) (Nat.le_max_right h h0)
    have actualObserved := stable r0 n0 (max p p0) (max h h0) k0
      (Nat.le_max_left p p0) (Nat.le_max_left h h0)
    have comparison : [.ok (fragment, returned)] = canonicalRaw ∧ reached = canonicalCaller ∧
        saved = _canonicalQueries ∧ read = _canonicalOuter ∧
        waiting = canonicalJoined.waiting ∧ after = _canonicalCache := by
      simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
        actualObserved.symm.trans canonicalObserved
    obtain ⟨rawSame, callerSame, _queriesSame, _outerSame, _waitingSame, _cacheSame⟩ := comparison
    have completedFold : canonicalFoldRows = [((), canonicalFolded)] := by
      rcases foldShape with rejected | completed
      · have emptyRaw := (rejectedBranch rejected).1
        have impossible : ([.ok (fragment, returned)] : List (Except EnumerationState.Error (Fragment × Core))) = [] := rawSame.trans emptyRaw
        cases impossible
      · exact completed
    obtain ⟨_incomingK, canonicalOldNode, canonicalOldScs, canonicalRead, canonicalAfter,
        canonicalReplacement, canonicalHandle, _afterCacheSame, _afterOuterSame, _reading,
        readFrame, _incomingRun, _writePrefix, _afterShape, canonicalStored, _afterStorage,
        _afterRealized, _incomingPost, _unfolding, _cacheRun, _afterCounter, representatives,
        _afterPaths, _afterCounts, _afterWaiting, _afterFlags, _expandable, rawShape,
        _fragmentBound, _replacementAvailable, _replacementClosed, _encoded,
        canonicalDecoded, noOld, oldCase⟩ := completedBranch completedFold
    have notEmpty : canonicalReplacement ≠ .empty := by
      intro emptyReplacement
      have emptyRaw : canonicalRaw = [] := rawShape.trans (ite_eq_left emptyReplacement)
      have impossible : ([.ok (fragment, returned)] : List (Except EnumerationState.Error (Fragment × Core))) = [] := rawSame.trans emptyRaw
      cases impossible
    have completeRaw : canonicalRaw = [.ok (.hole canonicalWinner, canonicalAfter.core)] :=
      rawShape.trans (ite_eq_right notEmpty)
    have rowSame : (fragment, returned) = (.hole canonicalWinner, canonicalAfter.core) :=
      Except.ok.inj (List.cons.inj (rawSame.trans completeRaw)).1
    have winnerSame : winner = canonicalWinner :=
      Fragments.Fragment.hole.inj (hole.symm.trans (Prod.mk.inj rowSame).1)
    have canonicalRoot : IsRoot returned.representatives canonicalWinner := by
      rw [(Prod.mk.inj rowSame).2, representatives]
      obtain ⟨size, path⟩ := foldedRoot
      exact ⟨size, (readFrame.reaches canonicalWinner canonicalWinner size).mpr path⟩
    obtain ⟨canonicalSize, canonicalPath⟩ := canonicalRoot
    have originalPath : UnionFind.Reaches returned.representatives canonicalWinner
        found.representative found.size := by
      simpa only [winnerSame] using actualPath
    have ownerSame : found.representative = canonicalWinner :=
      (UnionFind.reaches_unique originalPath canonicalPath).1
    have sameStored : returned.values[found.representative]? =
        some (.unenumerated (some canonicalHandle) (descendants ++ canonicalOldScs)) := by
      rw [ownerSame, (Prod.mk.inj rowSame).2]
      exact canonicalStored
    have samePayload : (UVarValue.unenumerated (some handle) (descendants ++ oldScs) : UVarValue Symbol) =
        .unenumerated (some canonicalHandle) (descendants ++ canonicalOldScs) :=
      Option.some.inj (installed.symm.trans sameStored)
    have handleSame : handle = canonicalHandle :=
      Option.some.inj (UVarValue.unenumerated.inj samePayload).1
    have decodedCanonical : SourcePruningEnumerationNodes.lookupNode
        reached.checked.native.machine.heap handle = some canonicalReplacement := by
      rw [handleSame, callerSame]
      exact canonicalDecoded
    have replacementSame : replacement = canonicalReplacement :=
      Option.some.inj (decoded.symm.trans decodedCanonical)
    intro ambient term member
    have canonicalMember : InternedGuardedLanguage.meaning
        (SourceEqualityPCSGuard.holds formulas solver) ambient canonicalReplacement term :=
      replacementSame ▸ member
    cases canonicalOldNode with
    | none =>
        rw [(noOld rfl).1] at canonicalMember
        exact canonicalMember
    | some oldHandle =>
        obtain ⟨_old, _query, _queried, _oldDecoded, _nextSource, _nextRoots,
          _receipt, intersection, _disabled⟩ := oldCase oldHandle rfl
        exact ((intersection ambient term).mp canonicalMember).1
  refine ⟨winner, found.representative, found.size, handle, descendants ++ oldScs, replacement,
    coreSame, hole, actualPath, installed, decoded, replacementAvailable, replacementClosed,
    (fun sc member terminalPath => (aliases sc member terminalPath).2.2.2), ?_, ?_⟩
  · intro ambient term member
    have markerAccepted := nativeRestriction ambient term member
    rw [markerEq] at markerAccepted
    exact nullaryMeaning markerEntry markerRow markerChildren (congrArg EdgeKey.symbol markerKey)
      (SourceEqualityPCSGuard.holds formulas solver) ambient term markerAccepted
  · intro ambient residualMeaning assignment satisfied
    have neutral := EnumerationFrame.neutralize_satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient reached.checked.native.machine.heap) residualMeaning assignment held returned satisfied
    have restrictions := (semantic ambient residualMeaning assignment fragment returned
      (List.mem_singleton_self _)).mp neutral
    have markerAccepted := restrictions.2.1
    rw [hole, fill, markerEq] at markerAccepted
    exact nullaryMeaning markerEntry markerRow markerChildren (congrArg EdgeKey.symbol markerKey)
      (SourceEqualityPCSGuard.holds formulas solver) ambient (assignment winner) markerAccepted

end MicroCFTA.SourceSynthesisCurrentUniverseTerminalMarkerNativeRestriction
