import MicroCFTA.SourcePruningEnumerationTerminalPrefixKeyAncestry
import MicroCFTA.SourcePruningEnumerationFoldKeyAncestry
import MicroCFTA.SourcePruningEnumerationFoldCacheBounds
import MicroCFTA.SourcePruningEnumerationIncomingKeyAncestry
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter

/-!
# Historical key shapes at actual terminal cache candidates

The actual prefix retains both ancestry fields.
Concrete fold and incoming observers retain the same original carrier.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
open EnumerationState EnumerationCorrectness SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable {carrier : List (List (List (List Nat)))}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- Every actual attached terminal cache retains its original historical key carrier. -/
theorem candidate_key_ancestry
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (proper : KeyAncestry carrier before.core)
    (after : Cached)
    (candidate : (run checkEmpty r n p h k first rest caller before incoming incomingScs queries).2 = some after) :
    KeyAncestry carrier after.core := by
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
      have joinedProper := SourcePruningEnumerationTerminalPrefix.run_key_ancestry r first rest before.waiting
        before.core joined recorded winner moved proper prefixSuccess
      rcases foldObserved : SourcePruningEnumerationCachedFold.run checkEmpty n p h recorded
          caller ⟨joined, before.expandable, moved⟩ winner queries with
        ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
      rw [foldObserved] at candidate
      have foldExact := (SourcePruningEnumerationCachedFold.erase checkEmpty n p h recorded
        caller ⟨joined, before.expandable, moved⟩ winner queries).symm.trans (congrArg Prod.fst foldObserved)
      have foldProper := SourcePruningEnumerationFold.run_key_ancestry checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedProper foldExact
      cases foldResult with
      | error fault => cases candidate
      | ok possible =>
        cases possible with
        | none => cases candidate
        | some raw =>
          cases raw with
          | nil =>
            apply SourcePruningEnumerationCachedFold.candidate_key_ancestry checkEmpty n p h recorded
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
                have foldedProper : KeyAncestry carrier folded := by simpa only [foldedSame] using foldProper
                cases foldCache with
                | none =>
                  dsimp only at candidate
                  rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                      foldCaller folded winner incoming incomingScs foldQueries with
                    ⟨incomingResult, reached, saved, read⟩
                  rw [incomingObserved] at candidate
                  cases incomingResult with
                  | error fault => cases candidate
                  | ok possible => cases possible <;> cases candidate
                | some recovered =>
                  dsimp only at candidate
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
                      apply SourcePruningEnumerationIncomingCacheAdapter.observed_cache_key_ancestry checkEmpty r n p h k
                        foldCaller (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs
                        foldQueries foldedProper after
                      rw [incomingObserved]
                      exact candidate
    next other => cases candidate

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
