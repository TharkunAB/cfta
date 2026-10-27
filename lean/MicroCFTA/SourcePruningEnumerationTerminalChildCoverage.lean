import MicroCFTA.SourcePruningEnumerationChildResources
import MicroCFTA.SourcePruningEnumerationCachedTerminalLanguage
import MicroCFTA.SourcePruningEnumerationTerminalBucketLanguage

/-!
# Term coverage of the actual resource-admitted terminal child

The original resource producer runs once and retains its complete packet.
An original satisfying assignment and accepted term exclude both terminal
rejection routes. The returned singleton uses the same caller and cache.
-/
namespace MicroCFTA.SourcePruningEnumerationChildCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original terminal restrictions force the same actual successful child singleton. -/
theorem complete_with_fragments_resources_terminal_accepting
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) bucket incoming beforeCaller before memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed bucket →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
        PendingFragment after.core fragment ∧
        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
          Avoids before.core.representatives held bucket →
          FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol) (term : Language.Term Symbol),
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true →
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming term →
        (∀ sc ∈ bucket, Suspended.Holds assignment term sc) →
        ∃ fragment : Fragment,
          raw = [.ok (fragment, after.core)] ∧ Fragments.fill assignment fragment = term ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting,
    observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, protects, references, history, shape, returnedFits, returnedKnown⟩ :=
    complete_with_fragments_resources seed formulas solver inventory beforeCaller before checkEmpty bucket incoming
      roots memos initial safe paths counts flags realized bounded pending available closed fits reserved known
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting,
    observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, protects, references, history, shape, returnedFits, returnedKnown, ?_⟩
  intro ambient residualMeaning assignment term terminalAny beforeSatisfied accepted holds
  have incomingNonempty : incoming ≠ .empty := by
    intro empty
    rw [empty, InternedGuardedLanguage.meaning] at accepted
    exact accepted
  have ranges := initial_ranges seed formulas solver inventory beforeCaller before checkEmpty bucket incoming roots memos
    initial safe paths counts bounded pending realized available closed fits reserved known
  cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
    cases here with
    | nil =>
      have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
        simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
      have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
        List.any_eq_false.mpr (List.filter_eq_nil_iff.mp filtered)
      rw [noTerminal] at terminalAny
      cases terminalAny
    | cons first rest =>
      have subsets := partition_subsets bucket first rest descendants partitioned
      have terminal : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
        simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
      have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
        fun sc member => bounded sc (subsets.1 member)
      have activePending : InputsPending before.core (first :: rest) := by
        intro held fragment stored sc member
        exact pending held fragment stored sc (subsets.1 member)
      obtain ⟨
        r0, n0, p0, h0, k0, recorded, winner, joined, foldRows, _foldCaller, _foldQueries, _foldFinal,
        _foldInventory, folded, canonicalRaw, reachedCaller, canonicalOuter, canonicalQueries, _final,
        _next, resultCache, _prefixRun, recordedSame, winnerMember, _movedSame, _joinedSame,
        _joinedFlagsSame, _prefixRoots, _prefixCounts, _joinedFlags, _cachedFoldRun, _foldRun, foldShape,
        _foldPost, _foldQuerySame, _foldCounter, _foldForest, _foldPaths, _foldStorage, _foldRealized,
        _foldedRoot, _foldPending, _foldCounts, _foldWaiting, _foldFlags, _foldEliminated,
        _foldCompleted, _foldedFrame, _foldedSafe, _foldedOrigin, _terminalRun, _post, _querySame,
        canonicalRun, _resultCounter, _resultPaths, _resultStorage, _resultRealized, _resultCounts,
        _resultFlags, _resultFrame, _resultSafe, _resultProtected, _resultOrigin, _resultAllowed,
        _rejectedCache, rejectedBranch, completedBranch, semantic⟩ :=
        SourcePruningEnumerationCachedTerminalAdapter.complete_semantics formulas solver inventory
          beforeCaller before checkEmpty first rest incoming descendants roots memos initial safe paths counts flags
          activeBounded activePending realized incomingNonempty available closed
          (fun sc member => bounded sc (subsets.2 member))
          (ranges incomingNonempty first rest descendants partitioned)
      have canonicalObserved :
          SourcePruningEnumerationChildDispatch.run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0)
            (k + k0) bucket incoming beforeCaller before memos.query =
            ((.ok (some canonicalRaw), reachedCaller, canonicalQueries, canonicalOuter, joined.waiting),
              some resultCache) := by
        rw [SourcePruningEnumerationChildDispatch.terminal checkEmpty _ _ _ _ _ bucket incoming
          beforeCaller before memos.query first rest descendants partitioned]
        simpa only [Nat.add_comm] using canonicalRun r n (max p p0) (max h h0) k
          (Nat.le_max_right p p0) (Nat.le_max_right h h0)
      have actualObserved := observed r0 n0 (max p p0) (max h h0) k0
        (Nat.le_max_left p p0) (Nat.le_max_left h h0)
      have same : raw = canonicalRaw ∧ afterCaller = reachedCaller ∧
          savedQueries = canonicalQueries ∧ outer = canonicalOuter ∧
          waiting = joined.waiting ∧ after = resultCache := by
        simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
          actualObserved.symm.trans canonicalObserved
      obtain ⟨rawSame, callerSame, _queriesSame, _outerSame, _waitingSame, cacheSame⟩ := same
      have winnerTerm : assignment winner = term := by
        rw [recordedSame] at winnerMember
        obtain ⟨chosen, member, named⟩ := List.mem_map.mp winnerMember
        have selectedTerminal : chosen ∈ bucket ∧ EqualityTrie.isTerminal chosen.trie = true := by
          apply List.mem_filter.mp
          rw [terminal]
          exact member
        have termChosen : term = assignment chosen.var :=
          (EnumerationSemantics.terminal_holds assignment term chosen selectedTerminal.2).mp
            (holds chosen selectedTerminal.1)
        obtain ⟨size, path⟩ := paths chosen.var
        have rootAssignment : assignment (roots chosen.var) = assignment chosen.var :=
          (beforeSatisfied.1.1 chosen.var (roots chosen.var)
            ⟨roots chosen.var, size, path, .root (UnionFind.reaches_terminal path)⟩).symm
        rw [← named]
        exact rootAssignment.trans termChosen.symm
      have restrictions := (SourcePruningEnumerationTerminalBucketLanguage.restrictions_iff
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core
        bucket first rest descendants roots recorded winner
        (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming)
        paths recordedSame winnerMember partitioned).mpr
          ⟨beforeSatisfied, by simpa only [winnerTerm] using accepted,
            fun sc member => by simpa only [winnerTerm] using holds sc member⟩
      obtain ⟨fragment, output, member, outputSatisfied⟩ :=
        (semantic ambient residualMeaning assignment).mpr restrictions
      have nonemptyRaw : canonicalRaw ≠ [] := by
        intro emptyRaw
        rw [emptyRaw] at member
        cases member
      have canonicalSingleton : canonicalRaw = [.ok (.hole winner, resultCache.core)] := by
        rcases foldShape with rejectedFold | completedFold
        · exact (nonemptyRaw (rejectedBranch rejectedFold).1).elim
        · obtain ⟨_incomingK, _oldNode, _oldScs, _read, written, replacement, _handle,
            writtenSame, _outerSame, _reading, _frame, _incomingRun, _writePrefix, _afterSame,
            _stored, _storage, _realized, _incomingPost, _unfolding, _cacheRun, _counter,
            _representatives, _paths, _counts, _waiting, _flags, _expandable, rawShape, _rest⟩ :=
              completedBranch completedFold
          by_cases replacementEmpty : replacement = .empty
          · have emptyRaw : canonicalRaw = [] := by
              simpa only [ite_eq_left replacementEmpty] using rawShape
            exact (nonemptyRaw emptyRaw).elim
          · simpa only [ite_eq_right replacementEmpty, writtenSame] using rawShape
      have outputSame : output = resultCache.core :=
        congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp
          (by simpa only [canonicalSingleton] using member)))
      refine ⟨.hole winner, ?_, ?_, ?_⟩
      · simpa only [cacheSame] using rawSame.trans canonicalSingleton
      · simpa only [Fragments.fill] using winnerTerm
      · simpa only [callerSame, cacheSame, outputSame] using outputSatisfied

end MicroCFTA.SourcePruningEnumerationChildCompletion
