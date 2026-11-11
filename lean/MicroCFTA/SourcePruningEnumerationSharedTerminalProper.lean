import MicroCFTA.SourcePruningEnumerationPrefixProper
import MicroCFTA.SourcePruningEnumerationSharedFoldProper
import MicroCFTA.SourcePruningEnumerationSharedIncomingProper

/-!
# Proper paths at the actual shared terminal candidate

The literal prefix and fold retain proper stored pending paths.
The shared incoming adapter retains strict descendant constraints.
Rejected raw-empty candidates need no safety conclusion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] sharedTerminalMonadList

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
      rcases foldObserved : fold checkEmpty n p h recorded
          caller ⟨joined, before.expandable, moved⟩ winner queries with
        ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
      rw [foldObserved] at candidate
      have foldExact := (fold_erase checkEmpty n p h recorded
        caller ⟨joined, before.expandable, moved⟩ winner queries).symm.trans (congrArg Prod.fst foldObserved)
      have foldProper := rawFold_proper checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedProper foldExact
      cases foldResult with
      | error fault => cases candidate
      | ok possible =>
        cases possible with
        | none => cases candidate
        | some raw =>
          cases raw with
          | nil =>
            apply fold_candidate_proper checkEmpty n p h recorded
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
                have foldedSame := rawFold_singleton_core checkEmpty n p h recorded
                  caller joined winner queries folded foldCaller foldQueries foldOuter foldExact
                have foldedProper : ProperState folded := by simpa only [foldedSame] using foldProper
                cases foldCache with
                | none =>
                  dsimp only at candidate
                  rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                      foldCaller folded winner incoming incomingScs foldQueries with
                    ⟨incomingResult, reached, saved, read⟩
                  rw [incomingObserved] at candidate
                  cases incomingResult with
                  | error fault => cases candidate
                  | ok possible => cases possible <;> cases candidate
                | some recovered =>
                  dsimp only at candidate
                  rcases incomingObserved : incomingCacheAdapter checkEmpty r n p h k
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
                      apply incoming_cache_proper checkEmpty r n p h k
                        foldCaller (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs
                        foldQueries foldedProper inputs after
                      rw [incomingObserved]
                      exact candidate
    next other => cases candidate


/-- The actual full-bucket partition supplies strict incoming descendants. -/
theorem candidate_partition_proper
    (checkEmpty : Bool) (r n p h k : Nat)
    (bucket : List Suspended) (first : Suspended) (rest descendants : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (queries : Queries)
    (proper : ProperState before.core) (inputs : ProperInputs bucket)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants))
    (after : Cached)
    (candidate : (run checkEmpty r n p h k first rest caller before incoming descendants queries).2 =
      some after) : ProperState after.core := by
  have below : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) = descendants := by
    simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
  have strict : ∀ sc ∈ descendants, ProperTrie sc.trie := by
    rw [← below]
    exact proper_below bucket inputs
  exact candidate_proper checkEmpty r n p h k first rest caller before incoming descendants queries
    proper strict after candidate

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
