import MicroCFTA.SourcePruningEnumerationChildCoverage
import MicroCFTA.SourcePruningEnumerationConstructorModelProgress
import MicroCFTA.SourcePruningEnumerationCachedTerminalStorageProgress

/-!
# Original accepting child models with storage progress

The original producer runs once and retains its entire result.
The added observer uses one assignment for meaning, fragment fill and cost.
Terminal children keep old values. Other children install one fresh value.
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

/-- Original accepted child terms yield one actual model and its pending-size bound. -/
theorem complete_with_fragments_resources_accepting_pendingSize
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
      (((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
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
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol) (term : Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming term →
        (∀ sc ∈ bucket, Suspended.Holds assignment term sc) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core ∧
          raw = [.ok (fragment, after.core)] ∧ Fragments.fill extended fragment = term ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol) (term : Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming term →
        (∀ sc ∈ bucket, Suspended.Holds assignment term sc) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core ∧
          raw = [.ok (fragment, after.core)] ∧ Fragments.fill extended fragment = term ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core ∧
          EnumerationStorageProgress.pendingSize after.core extended ≤
            EnumerationStorageProgress.pendingSize before.core assignment + NumberedTerms.size term := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, retained⟩ :=
    complete_with_fragments_resources_accepting seed formulas solver inventory beforeCaller before
      checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded pending
      available closed fits reserved known
  have resources := retained.1
  rcases resources with ⟨observed, _post, _query, _growth, _paths, _storage, _realized,
    _counts, _flags, _origin, _protects, _references, _history, _shape, _fits, _known, _terminal⟩
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, retained, ?_⟩
  intro ambient residualMeaning assignment term satisfied accepted held
  by_cases terminalAny : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
  · have incomingNonempty : incoming ≠ .empty := by
      intro empty
      rw [empty, InternedGuardedLanguage.meaning] at accepted
      exact accepted
    have ranges := initial_ranges seed formulas solver inventory beforeCaller before checkEmpty
      bucket incoming roots memos initial safe paths counts bounded pending realized available closed
      fits reserved known
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
          have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
            simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
          have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
            fun sc member => bounded sc (subsets.1 member)
          have activePending : InputsPending before.core (first :: rest) := by
            intro uv fragment stored sc member
            exact pending uv fragment stored sc (subsets.1 member)
          have activeTerminal : ∀ sc ∈ first :: rest, EqualityTrie.isTerminal sc.trie = true := by
            intro sc member
            have inFilter : sc ∈ bucket.filter (fun entry => EqualityTrie.isTerminal entry.trie) := by
              rw [filtered]
              exact member
            exact (List.mem_filter.mp inFilter).2
          obtain ⟨r0, n0, p0, h0, k0, recorded, winner, joined, foldRows, foldCaller,
            foldQueries, foldFinal, foldInventory, folded, canonicalRaw, reachedCaller,
            canonicalOuter, canonicalQueries, canonicalFinal, canonicalInventory, resultCache,
            receipt, costObserver⟩ :=
            SourcePruningEnumerationCachedTerminalAdapter.complete_semantics_pendingSize
              formulas solver inventory beforeCaller before checkEmpty first rest incoming descendants
              roots memos initial safe paths counts flags activeBounded activePending realized
              incomingNonempty available closed (fun sc member => bounded sc (subsets.2 member))
              (ranges incomingNonempty first rest descendants partitioned) activeTerminal
          rcases receipt with ⟨_prefixRun, _recordedSame, _winnerMember, _movedSame, _joinedSame,
            _joinedFlagsSame, _prefixRoots, _prefixCounts, _joinedFlags, _cachedFoldRun,
            _foldRun, _foldShape, _foldPost, _foldQuerySame, _foldCounter, _foldForest,
            _foldPaths, _foldStorage, _foldRealized, _foldedRoot, _foldPending, _foldCounts,
            _foldWaiting, _foldFlags, _foldEliminated, _foldCompleted, _foldedFrame, _foldedSafe,
            _foldedOrigin, _terminalRun, _post, _querySame, canonicalRun, _resultCounter,
            _resultPaths, _resultStorage, _resultRealized, _resultCounts, _resultFlags,
            _resultFrame, _resultSafe, _resultProtected, _resultOrigin, _resultAllowed,
            _rejectedCache, _rejectedBranch, _completedBranch, _semantic⟩
          have canonicalObserved :
              SourcePruningEnumerationChildDispatch.run checkEmpty (r + r0) (n + n0)
                (max p p0) (max h h0) (k + k0) bucket incoming beforeCaller before memos.query =
                ((.ok (some canonicalRaw), reachedCaller, canonicalQueries, canonicalOuter,
                  joined.waiting), some resultCache) := by
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
          obtain ⟨singleton, afterModel, filled, cost⟩ :=
            costObserver ambient residualMeaning assignment term satisfied accepted
              (fun sc member => held sc (subsets.1 member))
              (fun sc member => held sc (subsets.2 member))
          refine ⟨assignment, .hole winner, (fun _ _ => rfl), satisfied, ?_, filled, ?_, ?_⟩
          · simpa only [cacheSame] using rawSame.trans singleton
          · simpa only [callerSame, cacheSame] using afterModel
          · simpa only [cacheSame] using cost
  · have nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
      Bool.eq_false_iff.mpr terminalAny
    obtain ⟨_oldAssignment, fragment, _oldAgree, _oldOriginal, singleton, _oldFill, _oldModel⟩ :=
      retained.2 ambient residualMeaning assignment term satisfied accepted held
    have actual := observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
    simp only [Nat.add_zero, singleton] at actual
    have trace : SourcePruningEnumerationChildTraversal.Trace checkEmpty r n p h k
        [(incoming, bucket)] beforeCaller before memos.query [fragment] afterCaller after savedQueries :=
      .cons actual (.nil afterCaller after savedQueries)
    have genuine : ∀ value scs, (value, scs) ∈ [(incoming, bucket)] →
        Available beforeCaller.checked.native.machine.heap value ∧ value.free = [] ∧
        ∀ sc ∈ scs, sc.var < before.core.counter := by
      intro value scs member
      have same : (value, scs) = (incoming, bucket) := List.mem_singleton.mp member
      cases same
      exact ⟨available, closed, bounded⟩
    have noTerminal : ∀ value scs, (value, scs) ∈ [(incoming, bucket)] →
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
      intro value scs member
      have same : (value, scs) = (incoming, bucket) := List.mem_singleton.mp member
      cases same
      exact nonterminal
    obtain ⟨extended, packet, originalExtended, _callerSame, _querySame, _afterStorage,
      _afterRealized, afterModel, _bounds⟩ :=
      SourcePruningEnumerationConstructorModelProgress.trace_model_pendingSize trace
        (SourceEqualityPCSGuard.holds formulas solver) ambient residualMeaning assignment [term]
        initial.ready.semantic.ready.semantic.1.normal.facts.coherent safe.1 realized satisfied
        genuine noTerminal (.cons ⟨accepted, held⟩ .nil)
    rcases packet with ⟨_installed, agree, _counter, _aligned, _slots, filled, cost⟩
    have childFill : Fragments.fill extended fragment = term := by
      simpa only [List.map_cons, List.map_nil, List.cons.injEq, and_true] using filled
    refine ⟨extended, fragment, agree, originalExtended, singleton, childFill, afterModel, ?_⟩
    simpa only [NumberedTerms.forestSize, Nat.add_zero] using Nat.le_of_eq cost

end MicroCFTA.SourcePruningEnumerationChildCompletion
