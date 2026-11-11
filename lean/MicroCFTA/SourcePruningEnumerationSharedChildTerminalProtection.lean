import MicroCFTA.SourcePruningEnumerationSharedChildResources

/-!
# Terminal-subset protection at an actual shared child return

Fresh child preparation preserves every old allocated root.
The terminal receipt needs avoidance of its terminal partition only.
Current resources construct the receipt used to identify the supplied return.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual stable child return preserves every old root outside its terminal subset. -/
theorem stable_run_protects_terminal_avoiding_root
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (held : Nat) (inside : held < before.core.counter) (root : IsRoot before.core.representatives held)
    (avoids : Avoids before.core.representatives held
      (bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie)))
    (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
    (savedQueries : Queries) (outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (stable : ∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
      run checkEmpty (r + extraRepresentative) (n + extraNative) P H (k + extraIndex)
        bucket incoming beforeCaller before memos.query =
        ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) :
    EnumerationDriver.Protected held before.core after.core := by
  by_cases empty : incoming = .empty
  · subst incoming
    have actual := stable 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
    have cacheSame : after = before := by
      rw [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.empty] at actual
      exact Option.some.inj (congrArg Prod.snd actual).symm
    rw [cacheSame]
    exact EnumerationDriver.Protected.refl held before.core root
  · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
          simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
        have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
          List.any_eq_false.mpr (List.filter_eq_nil_iff.mp filtered)
        obtain ⟨action, km, preparedAfter, prepared, actionRun, preparedRun, _remaining⟩ :=
          nonterminal_complete checkEmpty r n p h bucket incoming beforeCaller before memos.query
            roots initial.ready.semantic.ready.semantic.1.normal.facts.coherent available closed
            empty safe.1 realized paths counts flags bounded noTerminal
        have success : Success action before.core (.hole before.core.counter) preparedAfter.core := by
          rw [Success, actionRun]
          simp
        have protects := (SourcePruningEnumerationChildEffects.child bucket incoming action
          before.core preparedAfter.core (.hole before.core.counter) safe bounded prepared success).2.2
        have actual := stable 0 0 p h km (Nat.le_refl _) (Nat.le_refl _)
        simp only [Nat.add_zero] at actual
        have built := preparedRun k
        rw [Nat.add_comm km k] at built
        have cacheSame : after = preparedAfter :=
          Option.some.inj (congrArg Prod.snd (actual.symm.trans built))
        simpa only [cacheSame] using protects held inside root
      | cons first rest =>
        have terminalPart : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) =
            first :: rest := by
          simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
        have descendantPart : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) =
            descendants := by
          simpa only [List.partition_eq_filter_filter, Function.comp_def] using
            congrArg Prod.snd partitioned
        have terminalSubset : (first :: rest) ⊆ bucket := by
          intro sc member
          exact (List.mem_filter.mp (terminalPart ▸ member)).1
        have descendantSubset : descendants ⊆ bucket := by
          intro sc member
          exact (List.mem_filter.mp (descendantPart ▸ member)).1
        have activePending : InputsPending before.core (first :: rest) := by
          intro target fragment stored sc member
          exact pending target fragment stored sc (terminalSubset member)
        have ranges := initial_ranges seed formulas solver inventory beforeCaller before checkEmpty
          bucket incoming roots memos initial safe paths counts bounded pending realized available
          closed fits reserved known
        obtain ⟨rm, nm, pm, hm, km, _recorded, _winner, joined, _foldRows, _foldCaller,
          _foldQueries, _foldFinal, _foldInventory, _folded, madeRaw, madeCaller, madeOuter,
          madeQueries, _madeFinal, _madeInventory, madeAfter,
          _prefixRun, _recordedSame, _winnerMember, _movedSame, _joinedSame, _joinedFlagsSame,
          _prefixRoots, _prefixCounts, _joinedFlags, _cachedFoldRun, _foldRun, _foldShape,
          _foldPost, _foldQuerySame, _foldCounter, _foldForest, _foldPaths, _foldStorage,
          _foldRealized, _foldedRoot, _foldPending, _foldCounts, _foldWaiting, _foldFlags,
          _foldEliminated, _foldCompleted, _foldedFrame, _foldedSafe, _foldedOrigin,
          _terminalRun, _post, _querySame, cacheRun, _counter, _afterPaths, _storage,
          _afterRealized, _afterCounts, _afterFlags, _outside, _afterSafe, protects, _remaining⟩ :=
          SourcePruningEnumerationSharedCachedTerminal.terminalAdapter_complete formulas solver
            inventory beforeCaller before checkEmpty first rest incoming descendants roots memos
            initial safe paths counts flags (fun sc member => bounded sc (terminalSubset member))
            activePending realized empty available closed
            (fun sc member => bounded sc (descendantSubset member))
            (ranges empty first rest descendants partitioned)
        have actual := stable rm nm (p + pm) (h + hm) km (by omega) (by omega)
        have built := cacheRun r n (p + pm) (h + hm) k (by omega) (by omega)
        rw [Nat.add_comm rm r, Nat.add_comm nm n, Nat.add_comm km k] at built
        have terminalRun : run checkEmpty (r + rm) (n + nm) (p + pm) (h + hm) (k + km)
            bucket incoming beforeCaller before memos.query =
            ((.ok (some madeRaw), madeCaller, madeQueries, madeOuter, joined.waiting),
              some madeAfter) := by
          rw [terminal checkEmpty _ _ _ _ _ bucket incoming beforeCaller before memos.query
            first rest descendants partitioned]
          exact built
        have cacheSame : after = madeAfter :=
          Option.some.inj (congrArg Prod.snd (actual.symm.trans terminalRun))
        have activeAvoid : Avoids before.core.representatives held (first :: rest) := by
          simpa only [terminalPart] using avoids
        simpa only [cacheSame] using protects held root activeAvoid

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
