import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources
import MicroCFTA.SourcePruningEnumerationCreatedIsolation

namespace MicroCFTA.SourcePruningEnumerationOpaqueEvent
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Staged" => List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment))
local notation "Trace" => SourcePruningEnumerationChildTraversal.Trace
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Split an actual completed trace at the selected child occurrence. -/
theorem split_event
    (checkEmpty : Bool) (r n p h k : Nat)
    (prefix suffix : List (Node × List Suspended)) (value : Node) (bucket : List Suspended)
    (caller afterCaller : Caller width) (before after : Cached) (queries afterQueries : Queries)
    (fragments : List Fragment)
    (trace : Trace checkEmpty r n p h k (prefix ++ (value, bucket) :: suffix)
      caller before queries fragments afterCaller after afterQueries) :
    ∃ (prefixFragments : List Fragment) (fragment : Fragment) (suffixFragments : List Fragment)
      (eventCaller preparedCaller : Caller width) (eventBefore prepared : Cached)
      (eventQueries preparedQueries : Queries) (outer : EnumerationState.State Symbol Constraint)
      (waiting : EnumerationWaitingIndex.Waiting),
      fragments = prefixFragments ++ fragment :: suffixFragments ∧
      Trace checkEmpty r n p h k prefix caller before queries
        prefixFragments eventCaller eventBefore eventQueries ∧
      SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket value
        eventCaller eventBefore eventQueries =
        ((.ok (some [.ok (fragment, prepared.core)]), preparedCaller, preparedQueries, outer, waiting),
          some prepared) ∧
      Trace checkEmpty r n p h k suffix preparedCaller prepared preparedQueries
        suffixFragments afterCaller after afterQueries := by
  induction prefix generalizing caller before queries fragments with
  | nil =>
      cases trace with
      | cons head tail =>
          exact ⟨[], _, _, _, _, _, _, _, _, _, _, rfl, .nil _ _ _, head, tail⟩
  | cons input prefix ih =>
      cases trace with
      | cons head tail =>
          obtain ⟨prefixFragments, fragment, suffixFragments, eventCaller, preparedCaller,
            eventBefore, prepared, eventQueries, preparedQueries, outer, waiting,
            fragmentSplit, prefixTrace, event, suffixTrace⟩ := ih _ _ _ _ tail
          refine ⟨_ :: prefixFragments, fragment, suffixFragments, eventCaller, preparedCaller,
            eventBefore, prepared, eventQueries, preparedQueries, outer, waiting,
            ?_, .cons head prefixTrace, event, suffixTrace⟩
          simpa only [List.cons_append] using congrArg (List.cons _) fragmentSplit

/-- A nonterminal successful row comes from the same cached preparation. -/
theorem nonterminal_child_row
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended) (value : Node)
    (caller reachedCaller : Caller width) (before after : Cached) (queries savedQueries : Queries)
    (fragment : Fragment) (outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (observed : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket value
      caller before queries =
      ((.ok (some [.ok (fragment, after.core)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap k
      bucket value before = some [(fragment, after)] ∧
      reachedCaller = caller ∧ savedQueries = queries ∧ outer = before.core ∧ waiting = before.waiting := by
  by_cases empty : value = .empty
  · simp [SourcePruningEnumerationChildDispatch.run, empty] at observed
  · have noHere : (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
      simp only [List.partition_eq_filter_filter]
      exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp nonterminal sc member)
    cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      have hereSame : here = [] := by simpa only [partitioned] using noHere
      subst here
      cases cached : SourcePruningEnumerationCachedPrepare.prepareChild
          caller.checked.native.machine.heap k bucket value before with
      | none =>
          simp only [SourcePruningEnumerationChildDispatch.run, ite_eq_right empty,
            partitioned, cached, Prod.mk.injEq, reduceCtorEq, and_false] at observed
      | some rows =>
          have erasure := SourcePruningEnumerationCachedPrepare.erase_some
            caller.checked.native.machine.heap k bucket value before rows cached
          cases actionEq : SourcePruningEnumerationShallowChild.prepareChild
              (EnumGuard := Constraint) bucket value with
          | none => simp only [actionEq, Option.map_none, reduceCtorEq] at erasure
          | some action =>
              have raw := congrArg (fun result => result.1.1) observed
              simp only [SourcePruningEnumerationChildDispatch.run,
                SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty, partitioned, actionEq] at raw
              simp only [actionEq, Option.map_some, Option.some.injEq] at erasure
              have rowsSame : rows.map (fun row => Except.ok (row.1, row.2.core)) =
                  [.ok (fragment, after.core)] :=
                erasure.symm.trans (Option.some.inj (Except.ok.inj raw))
              obtain ⟨row, singleton, mapped⟩ := List.map_eq_singleton_iff.mp rowsSame
              rcases row with ⟨childFragment, childCache⟩
              subst rows
              have cacheSame : childCache = after := by
                simpa only [SourcePruningEnumerationChildDispatch.run, ite_eq_right empty,
                  partitioned, cached, Option.some.injEq] using congrArg Prod.snd observed
              have fragmentSame : childFragment = fragment := (Prod.mk.inj (Except.ok.inj mapped)).1
              subst childCache
              subst childFragment
              refine ⟨cached, ?_⟩
              have endpoints := congrArg (fun result => (result.1.2.1, result.1.2.2)) observed
              simp only [SourcePruningEnumerationChildDispatch.run,
                SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty, partitioned,
                actionEq, Prod.mk.injEq] at endpoints
              obtain ⟨callerSame, queriesSame, outerSame, waitingSame⟩ := endpoints
              exact ⟨callerSame.symm, queriesSame.symm, outerSame.symm, waitingSame.symm⟩

/-- A completed captured edge retains its actual child trace and finalizer. -/
theorem captured_complete_trace
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller reachedCaller : Caller width)
    (before middle headCache : Cached) (queries savedQueries : Queries)
    (symbol : Symbol) (staged : Staged) (residual : Option Constraint) (fragment : Fragment)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)])
    (completed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge
      caller before queries = some (.complete fragment reachedCaller savedQueries headCache)) :
    ∃ (fragments : List Fragment) (childCache : Cached),
      fragment = .node symbol fragments ∧
      Trace checkEmpty r n p h k (staged.map (fun input => (input.1, input.2.1)))
        caller middle queries fragments reachedCaller childCache savedQueries ∧
      SourcePruningEnumerationFinalize.run reachedCaller.checked.native.machine.heap k target fragment
        (SourcePruningEnumerationSelectedEdge.finish residual fragment childCache) = some headCache := by
  unfold SourcePruningEnumerationCapturedEdge.run at completed
  simp only [SourcePruningEnumerationSelectedEdge.run, prepared] at completed
  cases childRun : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
  | stopped fragments observation candidate =>
      simp only [childRun, reduceCtorEq] at completed
  | complete fragments afterCaller afterQueries childCache =>
      simp only [childRun] at completed
      cases finalized : SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap
          k target (.node symbol fragments)
          (SourcePruningEnumerationSelectedEdge.finish residual (.node symbol fragments) childCache) with
      | none => simp only [finalized, Option.map_none, reduceCtorEq] at completed
      | some final =>
          simp only [finalized, Option.map_some, Option.some.injEq,
            SourcePruningEnumerationSelectedEdge.Result.complete.injEq] at completed
          obtain ⟨rfl, rfl, rfl, rfl⟩ := completed
          exact ⟨fragments, childCache, rfl,
            SourcePruningEnumerationChildTraversal.complete_trace checkEmpty r n p h k
              _ caller afterCaller middle childCache queries afterQueries fragments childRun,
            finalized⟩

end MicroCFTA.SourcePruningEnumerationOpaqueEvent
