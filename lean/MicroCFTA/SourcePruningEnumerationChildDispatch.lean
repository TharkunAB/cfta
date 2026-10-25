import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter

namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "PrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationState.State Symbol Constraint))
local notation "FoldRaw" => List (Except EnumerationState.Error
  (Unit × EnumerationState.State Symbol Constraint))
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
variable {width : Nat}
/-- Keep the complete raw child observation and its reached state. -/
abbrev Observation (width : Nat) :=
  (Except (PrefixRaw ⊕ ((SourceEqualityNativeDemand.Outcome width Node ⊕
    SourceCurrentAllocatedConjunctionWorker.Outcome width) ⊕ FoldRaw)) (Option TerminalRaw)) ×
    Caller width × Queries × EnumerationState.State Symbol Constraint × EnumerationWaitingIndex.Waiting
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Dispatch the actual child partition and retain the original raw observation. -/
noncomputable def observe
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting) (queries : Queries) : Observation width :=
  if incoming = .empty then
    (.ok (some []), beforeCaller, queries, before, waiting)
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        match SourcePruningEnumerationShallowChild.prepareChild scs incoming with
        | none => (.ok none, beforeCaller, queries, before, waiting)
        | some action => (.ok (some (ExceptT.run (action before))), beforeCaller, queries, before, waiting)
    | (first :: rest, descendants) =>
        SourcePruningEnumerationTerminal.run checkEmpty representativeFuel nativeFuel p h
          first rest waiting beforeCaller before incoming descendants queries

/-- Add the native cache while retaining terminal caller, query and raw effects. -/
noncomputable def run
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) : Observation width × Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  if incoming = .empty then
    ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before)
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        (observe checkEmpty representativeFuel nativeFuel p h scs incoming
          beforeCaller before.core before.waiting queries,
          match SourcePruningEnumerationCachedPrepare.prepareChild
              beforeCaller.checked.native.machine.heap indexFuel scs incoming before with
          | some [] => some before
          | some [(_, after)] => some after
          | _ => none)
    | (first :: rest, descendants) =>
        SourcePruningEnumerationCachedTerminalAdapter.run
          checkEmpty representativeFuel nativeFuel p h indexFuel
          first rest beforeCaller before incoming descendants queries

/-- Cache erasure preserves every raw result and reached caller at fixed bounds. -/
theorem erase
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) :
    (run checkEmpty representativeFuel nativeFuel p h indexFuel
      scs incoming beforeCaller before queries).1 =
      observe checkEmpty representativeFuel nativeFuel p h scs incoming
        beforeCaller before.core before.waiting queries := by
  by_cases empty : incoming = .empty
  · simp only [run, observe, ite_eq_left empty]
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil => simp only [run, ite_eq_right empty, partitioned]
      | cons first rest =>
        simpa only [run, observe, ite_eq_right empty, partitioned] using
          SourcePruningEnumerationCachedTerminalAdapter.erase
            checkEmpty representativeFuel nativeFuel p h indexFuel
            first rest beforeCaller before incoming descendants queries

/-- The terminal route retains the complete existing adapter and all its receipts. -/
theorem terminal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) (first : Suspended) (rest descendants : List Suspended)
    (partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants)) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming beforeCaller before queries =
      SourcePruningEnumerationCachedTerminalAdapter.run
        checkEmpty representativeFuel nativeFuel p h indexFuel
        first rest beforeCaller before incoming descendants queries := by
  by_cases empty : incoming = .empty
  · simp only [run, SourcePruningEnumerationCachedTerminalAdapter.run, ite_eq_left empty]
  · simp only [run, ite_eq_right empty, partitioned]

/-- Every successful singleton cache has the actual raw row core at fixed bounds. -/
theorem singleton_core
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller reachedCaller : Caller width)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries savedQueries : Queries) (fragment : Fragments.Fragment Symbol)
    (returned outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (observed : run checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming
      beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    after.core = returned := by
  by_cases empty : incoming = .empty
  · simp [run, empty] at observed
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | cons first rest =>
        apply SourcePruningEnumerationCachedTerminalAdapter.singleton_core checkEmpty
          representativeFuel nativeFuel p h indexFuel first rest beforeCaller reachedCaller
          before after incoming descendants queries savedQueries fragment returned outer waiting
        simpa only [run, ite_eq_right empty, partitioned] using observed
      | nil =>
        cases cached : SourcePruningEnumerationCachedPrepare.prepareChild
            beforeCaller.checked.native.machine.heap indexFuel scs incoming before with
        | none => simp only [run, ite_eq_right empty, partitioned, cached, Prod.mk.injEq,
            reduceCtorEq, and_false] at observed
        | some rows =>
          have erasure := SourcePruningEnumerationCachedPrepare.erase_some
            beforeCaller.checked.native.machine.heap indexFuel scs incoming before rows cached
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild
              (EnumGuard := Constraint) scs incoming with
          | none => simp only [prepared, Option.map_none, reduceCtorEq] at erasure
          | some action =>
            have raw := congrArg (fun result => result.1.1) observed
            simp only [run, observe, ite_eq_right empty, partitioned, prepared] at raw
            simp only [prepared, Option.map_some, Option.some.injEq] at erasure
            have rowsSame : rows.map (fun row => Except.ok (row.1, row.2.core)) =
                [.ok (fragment, returned)] :=
              erasure.symm.trans (Option.some.inj (Except.ok.inj raw))
            obtain ⟨row, singleton, mapped⟩ := List.map_eq_singleton_iff.mp rowsSame
            rcases row with ⟨childFragment, childCache⟩
            subst rows
            have cacheSame : childCache = after := by
              simpa only [run, ite_eq_right empty, partitioned, cached, Option.some.injEq] using
                congrArg Prod.snd observed
            subst after
            exact (Prod.mk.inj (Except.ok.inj mapped)).2

/-- Empty rejects before partition, prefix execution or any native query. -/
theorem empty
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel scs .empty beforeCaller before queries =
      ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before) := by
  simp only [run, ↓reduceIte]

/-- Genuine nonterminal inputs derive the same fresh child and its maintained indexes. -/
theorem nonterminal_complete
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent beforeCaller.checked.native.machine.heap)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = []) (nonempty : incoming ≠ .empty)
    (storage : StorageValid before.core)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ (action : EnumerateM Symbol Constraint (Fragments.Fragment Symbol)) (fuel : Nat)
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action ∧
      ExceptT.run (action before.core) = [.ok (.hole before.core.counter, after.core)] ∧
      (∀ (extra : Nat), run checkEmpty representativeFuel nativeFuel p h (fuel + extra)
        scs incoming beforeCaller before queries =
        ((.ok (some [.ok (.hole before.core.counter, after.core)]),
          beforeCaller, queries, before.core, before.waiting), some after)) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized beforeCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        beforeCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      FragmentBound («Symbol» := Symbol) after.core.counter (.hole before.core.counter) := by
  obtain ⟨action, fuel, rows, prepared, cachedRun, raw, shape⟩ :=
    SourcePruningEnumerationCachedPrepare.complete beforeCaller.checked.native.machine.heap
      before incoming scs roots coherent available closed storage realized paths counts flags bounded
      (fun _ => nonterminal)
  rcases shape with ⟨emptyValue, _emptyRows⟩ | ⟨after, _nonempty, rowsSame,
    grows, aligned, forestSame, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags, bound⟩
  · exact (nonempty emptyValue).elim
  · rw [rowsSame] at cachedRun raw
    have noHere : (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
      simp only [List.partition_eq_filter_filter]
      exact List.filter_eq_nil_iff.mpr (fun sc member =>
        List.any_eq_false.mp nonterminal sc member)
    refine ⟨action, fuel, after, prepared, ?_, ?_, grows, aligned, forestSame,
      afterPaths, afterStorage, afterRealized, afterCounts, afterFlags, bound⟩
    · simpa only [List.map_cons, List.map_nil] using raw
    · intro extra
      cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
      | mk here descendants =>
        have hereSame : here = [] := by simpa only [partitioned] using noHere
        subst here
        simp only [run, observe, ite_eq_right nonempty, partitioned, prepared,
          cachedRun extra, List.map_cons, List.map_nil, raw]

end MicroCFTA.SourcePruningEnumerationChildDispatch
