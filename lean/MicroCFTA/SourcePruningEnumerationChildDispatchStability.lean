import MicroCFTA.SourcePruningEnumerationChildDispatch
import MicroCFTA.SourcePruningEnumerationCachedTerminalStability
import MicroCFTA.SourcePruningEnumerationCachedPrepareStability

/-!
# Stable successful actual child points

The same successful raw row and cache survive independently larger bounds.
The proof follows the actual partition and cache adapter.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Fragments.Fragment Symbol × Core))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The successful raw child observation retains every field at larger bounds. -/
theorem observe_ok_stable
    {checkEmpty : Bool} {r R n N p P h H : Nat}
    {scs : List Suspended} {incoming : Node} {beforeCaller afterCaller : Caller width}
    {before outer : Core} {waiting moved : EnumerationWaitingIndex.Waiting}
    {queries savedQueries : Queries} {raw : Raw}
    (observed : observe checkEmpty r n p h scs incoming beforeCaller before waiting queries =
      (.ok (some raw), afterCaller, savedQueries, outer, moved))
    (successful : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)])
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    observe checkEmpty R N P H scs incoming beforeCaller before waiting queries =
      (.ok (some raw), afterCaller, savedQueries, outer, moved) := by
  by_cases empty : incoming = .empty
  · simpa only [observe, ite_eq_left empty] using observed
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk active descendants =>
      cases active with
      | nil =>
        simpa only [observe, ite_eq_right empty, partitioned] using observed
      | cons first rest =>
        have terminalObserved : SourcePruningEnumerationTerminal.run checkEmpty r n p h
            first rest waiting beforeCaller before incoming descendants queries =
            (.ok (some raw), afterCaller, savedQueries, outer, moved) := by
          simpa only [observe, ite_eq_right empty, partitioned] using observed
        simpa only [observe, ite_eq_right empty, partitioned] using
          SourcePruningEnumerationTerminal.run_ok_stable terminalObserved successful
            enoughRepresentative enoughNative enoughP enoughH

/-- The actual successful child row and its cache are stable at independently larger bounds. -/
theorem run_some_stable
    {checkEmpty : Bool} {r R n N p P h H k K : Nat}
    {scs : List Suspended} {incoming : Node} {beforeCaller afterCaller : Caller width}
    {before after : Cached} {outer : Core} {moved : EnumerationWaitingIndex.Waiting}
    {queries savedQueries : Queries} {raw : Raw}
    (observed : run checkEmpty r n p h k scs incoming beforeCaller before queries =
      ((.ok (some raw), afterCaller, savedQueries, outer, moved), some after))
    (successful : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)])
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    run checkEmpty R N P H K scs incoming beforeCaller before queries =
      ((.ok (some raw), afterCaller, savedQueries, outer, moved), some after) := by
  by_cases empty : incoming = .empty
  · simpa only [run, ite_eq_left empty] using observed
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk active descendants =>
      cases active with
      | cons first rest =>
        have terminalObserved : SourcePruningEnumerationCachedTerminalAdapter.run
            checkEmpty r n p h k first rest beforeCaller before incoming descendants queries =
            ((.ok (some raw), afterCaller, savedQueries, outer, moved), some after) := by
          simpa only [run, ite_eq_right empty, partitioned] using observed
        simpa only [run, ite_eq_right empty, partitioned] using
          SourcePruningEnumerationCachedTerminalAdapter.run_some_stable terminalObserved successful
            enoughRepresentative enoughNative enoughP enoughH enoughIndex
      | nil =>
        have originalObserved : observe checkEmpty r n p h scs incoming
            beforeCaller before.core before.waiting queries =
            (.ok (some raw), afterCaller, savedQueries, outer, moved) :=
          (erase checkEmpty r n p h k scs incoming beforeCaller before queries).symm.trans
            (congrArg Prod.fst observed)
        have originalLater := observe_ok_stable originalObserved successful
          enoughRepresentative enoughNative enoughP enoughH
        cases cachedObserved : SourcePruningEnumerationCachedPrepare.prepareChild
            beforeCaller.checked.native.machine.heap k scs incoming before with
        | none =>
          simp only [run, ite_eq_right empty, partitioned, cachedObserved,
            Prod.mk.injEq, reduceCtorEq, and_false] at observed
        | some rows =>
          have cachedLater := SourcePruningEnumerationCachedPrepare.prepareChild_some_stable
            cachedObserved enoughIndex
          simpa only [run, ite_eq_right empty, partitioned, cachedObserved, cachedLater,
            originalObserved, originalLater] using observed

/-- A literal successful child singleton keeps its complete cache and raw endpoint. -/
theorem run_singleton_stable
    {checkEmpty : Bool} {r R n N p P h H k K : Nat}
    {scs : List Suspended} {incoming : Node} {beforeCaller afterCaller : Caller width}
    {before after : Cached} {outer returned : Core} {moved : EnumerationWaitingIndex.Waiting}
    {queries savedQueries : Queries} {fragment : Fragments.Fragment Symbol}
    (observed : run checkEmpty r n p h k scs incoming beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), afterCaller, savedQueries, outer, moved), some after))
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    run checkEmpty R N P H K scs incoming beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), afterCaller, savedQueries, outer, moved), some after) :=
  run_some_stable observed (.inr ⟨fragment, returned, rfl⟩)
    enoughRepresentative enoughNative enoughP enoughH enoughIndex

end MicroCFTA.SourcePruningEnumerationChildDispatch
