import MicroCFTA.SourcePruningEnumerationFoldCacheBounds
import MicroCFTA.SourcePruningEnumerationTerminalPrefixBounds
import MicroCFTA.SourcePruningEnumerationIncomingCacheBounds

/-!
# Scalar bounds for actual terminal cache returns

The terminal prefix and source fold preserve suspended mass. The incoming
write adds its own bucket. Rejected folds retain their actual prefix cache.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual returned terminal cache retains its counter and adds at most the incoming bucket. -/
theorem observed_cache_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (beforeCaller : Caller width) (before : Cached) (incoming : Node)
    (incomingScs : List Suspended) (queries : Queries) (after : Cached)
    (observed : (run checkEmpty r n p h k first rest beforeCaller before
      incoming incomingScs queries).2 = some after) :
    after.core.counter = before.core.counter ∧
      suspendedBound after.core ≤ suspendedBound before.core + incomingScs.length := by
  by_cases empty : incoming = .empty
  · simp only [run, ite_eq_left empty, Option.some.injEq] at observed
    subst after
    exact ⟨rfl, Nat.le_add_right _ _⟩
  · cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        r first rest before.waiting before.core) with
    | nil => simp only [run, ite_eq_right empty, prefixObserved] at observed; cases observed
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error fault => simp only [run, ite_eq_right empty, prefixObserved] at observed; cases observed
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
        cases prefixTail with
        | cons second remaining =>
          simp only [run, ite_eq_right empty, prefixObserved] at observed
          cases observed
        | nil =>
          have prefixBounds := SourcePruningEnumerationTerminalPrefix.observed_counter_mass
            r first rest before.waiting before.core joined (recorded, winner, moved) prefixObserved
          rcases foldObserved : SourcePruningEnumerationCachedFold.run checkEmpty n p h recorded
              beforeCaller ⟨joined, before.expandable, moved⟩ winner queries with
            ⟨⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
          simp only [run, ite_eq_right empty, prefixObserved, foldObserved] at observed
          cases foldOutcome with
          | error fault => cases observed
          | ok possible =>
            cases possible with
            | none => cases observed
            | some foldRaw =>
              cases foldRaw with
              | nil =>
                have foldBounds := SourcePruningEnumerationCachedFold.observed_cache_bounds
                  checkEmpty n p h recorded beforeCaller ⟨joined, before.expandable, moved⟩
                  winner queries after (by rw [foldObserved]; exact observed)
                exact ⟨foldBounds.1.trans prefixBounds.1, by
                  rw [foldBounds.2, prefixBounds.2]
                  exact Nat.le_add_right _ _⟩
              | cons foldEntry foldTail =>
                cases foldEntry with
                | error fault => cases observed
                | ok foldPair =>
                  rcases foldPair with ⟨foldUnit, folded⟩
                  cases foldUnit
                  cases foldTail with
                  | cons second remaining => cases observed
                  | nil =>
                    have erased := SourcePruningEnumerationCachedFold.erase checkEmpty n p h recorded
                      beforeCaller ⟨joined, before.expandable, moved⟩ winner queries
                    rw [foldObserved] at erased
                    have foldedSame := SourcePruningEnumerationFold.singleton_core
                      checkEmpty n p h recorded beforeCaller joined winner queries
                      folded foldCaller foldQueries foldOuter erased.symm
                    have foldBounds := SourcePruningEnumerationFold.observed_counter_mass
                      checkEmpty n p h recorded beforeCaller joined winner queries
                      (.ok (some [.ok ((), folded)])) foldCaller foldQueries foldOuter erased.symm
                    cases foldCache with
                    | none =>
                      dsimp only at observed
                      rcases incomingObserved : SourcePruningEnumerationIncomingNode.run
                          checkEmpty r n p h foldCaller folded winner incoming incomingScs foldQueries with
                        ⟨incomingOutcome, reachedCaller, savedQueries, read⟩
                      cases incomingOutcome with
                      | error fault => simp only [incomingObserved] at observed; cases observed
                      | ok possible =>
                        cases possible <;> simp only [incomingObserved] at observed <;> cases observed
                    | some recovered =>
                      dsimp only at observed
                      rcases incomingObserved : SourcePruningEnumerationIncomingCacheAdapter.run
                          checkEmpty r n p h k foldCaller (EnumerationExpandableIndex.frame folded recovered)
                          winner incoming incomingScs foldQueries with
                        ⟨⟨incomingOutcome, reachedCaller, savedQueries, read⟩, incomingCache⟩
                      cases incomingOutcome with
                      | error fault => simp only [incomingObserved] at observed; cases observed
                      | ok possible =>
                        cases possible with
                        | none => simp only [incomingObserved] at observed; cases observed
                        | some raw =>
                          simp only [incomingObserved] at observed
                          have incomingBounds := SourcePruningEnumerationIncomingCacheAdapter.observed_cache_bounds
                            checkEmpty r n p h k foldCaller (EnumerationExpandableIndex.frame folded recovered)
                            winner incoming incomingScs foldQueries after
                            (by rw [incomingObserved]; exact observed)
                          dsimp only [EnumerationExpandableIndex.frame] at incomingBounds
                          rw [foldedSame, foldBounds.1, foldBounds.2, prefixBounds.1, prefixBounds.2] at incomingBounds
                          exact ⟨incomingBounds.1, Nat.le_of_eq incomingBounds.2⟩

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
