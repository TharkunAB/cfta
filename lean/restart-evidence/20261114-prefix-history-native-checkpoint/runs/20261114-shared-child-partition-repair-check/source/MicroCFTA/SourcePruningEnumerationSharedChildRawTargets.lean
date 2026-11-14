import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationTerminalPrefixRawTargets
import MicroCFTA.SourcePruningEnumerationSharedTerminalScalarBounds

/-!
# Raw targets at an actual shared terminal child

The actual shared result supplies its terminal partition and prefix return.
The recorded list retains every input occurrence in order.
The prefix joins each raw target to the returned fragment's winner.
The shared fold and incoming call retain their actual endpoints.
Alias preservation after the prefix and the full branch history remain open.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol

set_option autoImplicit false
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem raw_terminal_singleton_interval
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (descendants : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (read after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (observed : SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty r n p h
      first rest waiting caller before incoming descendants queries =
        (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, read, moved)) :
    ∃ (recorded : List Nat) (winner : Nat) (joined : Core)
        (foldCaller : Caller width) (foldQueries : Queries) (folded foldOuter : Core),
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)] ∧
      SourcePruningEnumerationSharedCachedTerminal.rawFold
        checkEmpty n p h recorded caller joined winner queries =
          (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, foldOuter) ∧
      folded = foldOuter ∧
      SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
        foldCaller folded winner incoming descendants foldQueries =
          (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read) ∧
      fragment = .hole winner := by
  unfold SourcePruningEnumerationSharedCachedTerminal.raw at observed
  split at observed
  next empty => cases observed
  next nonempty =>
    split at observed
    next recorded winner transfer joined prefixObserved =>
      rcases foldObserved : SourcePruningEnumerationSharedCachedTerminal.rawFold
          checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observed
      cases foldResult with
      | error fault => cases observed
      | ok possible =>
          cases possible with
          | none => cases observed
          | some raw =>
              dsimp only at observed
              split at observed
              next empty => cases observed
              next folded =>
                have foldEndpoint :=
                  SourcePruningEnumerationSharedCachedTerminal.rawFold_singleton_core
                    checkEmpty n p h recorded caller joined winner queries
                    folded foldCaller foldQueries foldOuter foldObserved
                rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run
                    checkEmpty r n p h foldCaller folded winner incoming descendants foldQueries with
                  ⟨incomingResult, reached, saved, currentRead⟩
                rw [incomingObserved] at observed
                cases incomingResult with
                | error fault => cases observed
                | ok result =>
                    cases result with
                    | none => cases observed
                    | some incomingRaw =>
                        have rowsSame := congrArg Prod.fst observed
                        dsimp only at rowsSame
                        have mapped := Option.some.inj (Except.ok.inj rowsSame)
                        have single : incomingRaw = [.ok ((), after)] := by
                          cases incomingRaw with
                          | nil => cases mapped
                          | cons row tail =>
                              cases row with
                              | error fault => cases mapped
                              | ok value =>
                                  rcases value with ⟨⟨⟩, returned⟩
                                  have fields := List.cons.inj mapped
                                  have coreSame : returned = after :=
                                    (Prod.mk.inj (Except.ok.inj fields.1)).2
                                  have tailEmpty : tail = [] := List.map_eq_nil_iff.mp fields.2
                                  simp only [coreSame, tailEmpty]
                        have reachedSame : reached = afterCaller :=
                          congrArg (fun result => result.2.1) observed
                        have savedSame : saved = savedQueries :=
                          congrArg (fun result => result.2.2.1) observed
                        have readSame : currentRead = read :=
                          congrArg (fun result => result.2.2.2.1) observed
                        have transferSame : transfer = moved :=
                          congrArg (fun result => result.2.2.2.2) observed
                        have fragmentSame : fragment = .hole winner := by
                          rw [single] at mapped
                          exact (Prod.mk.inj (Except.ok.inj (List.cons.inj mapped).1)).1.symm
                        rw [transferSame] at prefixObserved
                        rw [single, reachedSame, savedSame, readSame] at incomingObserved
                        exact ⟨recorded, winner, joined, foldCaller, foldQueries, folded, foldOuter,
                          prefixObserved, foldObserved, foldEndpoint, incomingObserved, fragmentSame⟩
              next other => cases observed
    next other => cases observed

/-- Actual shared child success identifies every raw target joined for its returned hole. -/
theorem terminal_singleton_raw_target_incidence
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended)
    (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (read after : Core) (moved : EnumerationWaitingIndex.Waiting) (afterCache : Option Cached)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (actual : run checkEmpty r n p h k bucket incoming caller before queries =
      ((.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, read, moved), afterCache)) :
    ∃ (first : Suspended) (rest descendants : List Suspended)
        (recorded : List Nat) (winner : Nat) (joined : Core)
        (foldCaller : Caller width) (foldQueries : Queries) (folded foldOuter : Core),
      bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
        (first :: rest, descendants) ∧
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        r first rest before.waiting before.core) =
        [.ok ((recorded, winner, moved), joined)] ∧
      SourcePruningEnumerationSharedCachedTerminal.rawFold
        checkEmpty n p h recorded caller joined winner queries =
          (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, foldOuter) ∧
      folded = foldOuter ∧
      SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
        foldCaller folded winner incoming descendants foldQueries =
          (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read) ∧
      recorded = (bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie)).map
        (fun sc => roots sc.var) ∧
      joined.values = before.core.values ∧ fragment = .hole winner ∧
      ∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
        UnionFind.SameClass joined.representatives winner sc.var := by
  have erased := erase checkEmpty r n p h k bucket incoming caller before queries
  rw [actual] at erased
  have observed : observe checkEmpty r n p h bucket incoming caller
      before.core before.waiting queries =
        (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, read, moved) := erased.symm
  have nonempty : incoming ≠ .empty := by
    intro empty
    subst incoming
    have impossible := congrArg Prod.fst observed
    simp only [observe, ite_true] at impossible
    cases impossible
  cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
      cases here with
      | nil =>
          have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
            simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
          have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
            List.any_eq_false.mpr (List.filter_eq_nil_iff.mp filtered)
          rw [noTerminal] at terminal
          cases terminal
      | cons first rest =>
          have terminalObserved : SourcePruningEnumerationSharedCachedTerminal.raw
              checkEmpty r n p h first rest before.waiting caller before.core
              incoming descendants queries =
                (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, read, moved) := by
            simpa only [observe, nonempty, ite_false, partitioned] using observed
          obtain ⟨recorded, winner, joined, foldCaller, foldQueries, folded, foldOuter,
              processed, foldedCall, foldEndpoint, incomingCall, hole⟩ :=
            raw_terminal_singleton_interval checkEmpty r n p h first rest before.waiting caller
              before.core incoming descendants queries fragment afterCaller savedQueries
              read after moved terminalObserved
          obtain ⟨recordedSame, joinedValues, rawTargets⟩ :=
            SourcePruningEnumerationTerminalPrefix.run_raw_target_incidence
              r first rest before.waiting before.core joined recorded winner moved roots paths processed
          have terminalMembers :
              bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
            simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
          refine ⟨first, rest, descendants, recorded, winner, joined,
            foldCaller, foldQueries, folded, foldOuter, rfl, processed,
            foldedCall, foldEndpoint, incomingCall, ?_, joinedValues, hole, ?_⟩
          · rw [terminalMembers]
            exact recordedSame
          · intro sc present atRoot
            apply rawTargets sc
            rw [← terminalMembers]
            apply List.mem_filter.mpr
            refine ⟨present, ?_⟩
            simp only [(EqualityTrie.nil_mem sc.trie).mp atRoot, EqualityTrie.isTerminal]

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch

#check @MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_raw_target_incidence
#print axioms MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_raw_target_incidence
