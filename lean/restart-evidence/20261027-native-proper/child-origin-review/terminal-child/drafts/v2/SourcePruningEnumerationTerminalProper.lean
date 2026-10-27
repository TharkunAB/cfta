import MicroCFTA.SourcePruningEnumerationPrefixProper
import MicroCFTA.SourcePruningEnumerationFoldProper
import MicroCFTA.SourcePruningEnumerationFoldCacheBounds
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
import MicroCFTA.SourcePruningEnumerationIncomingProper

/-!
# ProperState tries in actual successful terminal rows

The actual prefix supplies the proper joined state.
The fold and incoming observation supply the exact successful row.
No rejected state is treated as an accepted row.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics EnumerationProgress
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] terminalMonadList

/-- An actual successful terminal row retains proper stored suspended tries. -/
theorem successful_proper
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (outer after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (canonical : ProperState before) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie)
    (observed : run checkEmpty r n p h first rest waiting caller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, outer, moved)) : ProperState after := by
  unfold run at observed
  split at observed
  next empty => cases observed
  next nonempty =>
    split at observed
    next recorded winner transfer joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest waiting)
          before (recorded, winner, transfer) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedProperState := SourcePruningEnumerationTerminalPrefix.run_proper r first rest waiting
        before joined recorded winner transfer canonical prefixSuccess
      rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observed
      have foldProperState := SourcePruningEnumerationFold.run_proper checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedProperState foldObserved
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
            have foldedSame := SourcePruningEnumerationFold.singleton_core checkEmpty n p h recorded
              caller joined winner queries folded foldCaller foldQueries foldOuter foldObserved
            have foldedProperState : ProperState folded := by simpa only [foldedSame] using foldProperState
            have incomingProperState := SourcePruningEnumerationIncomingNode.run_proper checkEmpty r n p h
              foldCaller folded winner incoming incomingScs foldQueries foldedProperState inputs
            rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                foldCaller folded winner incoming incomingScs foldQueries with
              ⟨incomingResult, reached, saved, read⟩
            rw [incomingObserved] at observed incomingProperState
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
                  | cons row rest =>
                    cases row with
                    | error error => cases mapped
                    | ok value =>
                      rcases value with ⟨⟨⟩, returned⟩
                      have fields := List.cons.inj mapped
                      have coreSame : returned = after := (Prod.mk.inj (Except.ok.inj fields.1)).2
                      have restEmpty : rest = [] := List.map_eq_nil_iff.mp fields.2
                      simp only [coreSame, restEmpty]
                exact incomingProperState.2 after (by rw [single])
          next other => cases observed
    next other => cases observed

end MicroCFTA.SourcePruningEnumerationTerminal

namespace MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
open EnumerationState EnumerationCorrectness EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- Every actual attached terminal cache retains proper paths, including rejected prefix caches. -/
theorem candidate_proper
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (proper : ProperState before.core)
    (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie) (after : Cached)
    (candidate : (run checkEmpty r n p h k first rest caller before incoming incomingScs queries).2 = some after) :
    ProperState after.core := by
  unfold run at candidate
  split at candidate
  next empty =>
    have same : before = after := Option.some.inj candidate
    subst after
    exact proper
  next nonempty =>
    split at candidate
    next recorded winner moved joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting)
          before.core (recorded, winner, moved) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedProper := SourcePruningEnumerationTerminalPrefix.run_proper r first rest before.waiting
        before.core joined recorded winner moved proper prefixSuccess
      rcases foldObserved : SourcePruningEnumerationCachedFold.run checkEmpty n p h recorded
          caller ⟨joined, before.expandable, moved⟩ winner queries with
        ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
      rw [foldObserved] at candidate
      have foldExact := (SourcePruningEnumerationCachedFold.erase checkEmpty n p h recorded
        caller ⟨joined, before.expandable, moved⟩ winner queries).symm.trans (congrArg Prod.fst foldObserved)
      have foldProper := SourcePruningEnumerationFold.run_proper checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedProper foldExact
      cases foldResult with
      | error fault => cases candidate
      | ok possible =>
        cases possible with
        | none => cases candidate
        | some raw =>
          cases raw with
          | nil =>
            apply SourcePruningEnumerationCachedFold.candidate_proper checkEmpty n p h recorded
              caller ⟨joined, before.expandable, moved⟩ winner queries joinedProper after
            rw [foldObserved]
            exact candidate
          | cons row tail =>
            cases row with
            | error fault => cases candidate
            | ok payload =>
              rcases payload with ⟨⟨⟩, folded⟩
              cases tail with
              | cons next later => cases candidate
              | nil =>
                have foldedSame := SourcePruningEnumerationFold.singleton_core checkEmpty n p h recorded
                  caller joined winner queries folded foldCaller foldQueries foldOuter foldExact
                have foldedProper : ProperState folded := by simpa only [foldedSame] using foldProper
                cases foldCache with
                | none => cases candidate
                | some recovered =>
                  rcases incomingObserved : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
                      foldCaller (EnumerationExpandableIndex.frame folded recovered)
                      winner incoming incomingScs foldQueries with
                    ⟨⟨incomingResult, reached, saved, read⟩, incomingCache⟩
                  rw [incomingObserved] at candidate
                  cases incomingResult with
                  | error fault => cases candidate
                  | ok possible =>
                    cases possible with
                    | none => cases candidate
                    | some incomingRaw =>
                      apply SourcePruningEnumerationIncomingCacheAdapter.observed_cache_proper checkEmpty r n p h k
                        foldCaller (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs
                        foldQueries foldedProper inputs after
                      rw [incomingObserved]
                      exact candidate
    next other => cases candidate

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
