import MicroCFTA.SourcePruningEnumerationSharedChildRawTargets
import MicroCFTA.SourcePruningEnumerationSharedFoldState

/-!
# Raw target aliases at the actual shared child's final Core

The completed shared fold keeps the representative forest.
The incoming lookup preserves existing root paths.
The completed incoming write keeps the compressed forest.
Each original terminal occurrence retains its raw target at both endpoints.
The full emitted history and finite joint completion remain open.
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

private theorem finish_singleton_forest
    {before returned : Core} {target handle : Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (observed : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before) = [.ok ((), returned)]) :
    returned.representatives = before.representatives := by
  let written : Core := {before with
    values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
      else before.recursionAncestry other}
  have rawRun : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  rw [rawRun] at observed
  have coreSame : written = returned := by
    split at observed
    · cases observed
    · exact (Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)).2
  rw [← coreSame]

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem shared_fold_singleton_forest
    (checkEmpty : Bool) (n p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Core) (target : Nat) (queries : Queries)
    (returned : Core) (afterCaller : Caller width) (savedQueries : Queries) (outer : Core)
    (observed : SourcePruningEnumerationSharedCachedTerminal.rawFold
      checkEmpty n p h sources caller before target queries =
        (.ok (some [.ok ((), returned)]), afterCaller, savedQueries, outer)) :
    returned.representatives = before.representatives := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, Prod.mk.injEq,
        Except.ok.injEq, Option.some.injEq, List.cons.injEq, and_true, true_and] at observed
      rcases observed with ⟨rfl, _callerSame, _queriesSame, rfl⟩
      rfl
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch
          checkEmpty n p h caller before source target queries with
        ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved] at observed
          cases observed
      | ok possible =>
          cases possible with
          | none =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved] at observed
              cases observed
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold,
                    dispatchObserved, rawObserved] at observed
                  cases observed
              | cons first tail =>
                  cases first with
                  | error fault =>
                      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold,
                        dispatchObserved, rawObserved] at observed
                      cases observed
                  | ok pair =>
                      rcases pair with ⟨⟨⟩, middle⟩
                      cases tail with
                      | cons second remaining =>
                          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold,
                            dispatchObserved, rawObserved] at observed
                          cases observed
                      | nil =>
                          have frame := SourcePruningEnumerationSharedFoldState.dispatch_frame
                            checkEmpty n p h caller before source target queries action
                            reachedCaller saved middle dispatchObserved rawObserved
                          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold,
                            dispatchObserved, rawObserved] at observed
                          exact (ih reachedCaller middle saved observed).trans frame.representatives

private theorem shared_incoming_singleton_aliases
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (returned : Core) (afterCaller : Caller width) (savedQueries : Queries) (read : Core)
    (observed : SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty r n p h caller before target incoming incomingScs queries =
        (.ok (some [.ok ((), returned)]), afterCaller, savedQueries, read)) :
    returned.representatives = read.representatives ∧
      ∀ left right, UnionFind.SameClass before.representatives left right →
        UnionFind.SameClass read.representatives left right := by
  unfold SourcePruningEnumerationSharedIncomingNode.run at observed
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
      simp only [lookup] at observed
      cases observed
  | some found =>
      simp only [lookup] at observed
      repeat' split at observed
      all_goals
        have resultSame := congrArg Prod.fst observed
        dsimp only at resultSame
        try (solve | simp at resultSame)
      all_goals
        have readSame := congrArg (fun result : _ × Caller width × Queries × Core =>
          result.2.2.2) observed
        dsimp only at readSame
        have writtenForest : returned.representatives = found.forest :=
          finish_singleton_forest (before := {before with representatives := found.forest})
            (Option.some.inj (Except.ok.inj resultSame))
        refine ⟨writtenForest.trans (congrArg (fun state : Core => state.representatives) readSame), ?_⟩
        intro left right related
        obtain ⟨root, size, leftPath, rightPath⟩ := related
        rw [← readSame]
        exact ⟨root, size,
          (UnionFind.findRoot_correct r before.representatives target found lookup).2 leftPath,
          (UnionFind.findRoot_correct r before.representatives target found lookup).2 rightPath⟩

/-- Every original terminal raw target remains aliased at the actual read and returned Core. -/
theorem terminal_singleton_final_raw_target_incidence
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
      folded.representatives = joined.representatives ∧
      after.representatives = read.representatives ∧
      ∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
        UnionFind.SameClass joined.representatives winner sc.var ∧
        UnionFind.SameClass folded.representatives winner sc.var ∧
        UnionFind.SameClass read.representatives winner sc.var ∧
        UnionFind.SameClass after.representatives winner sc.var := by
  obtain ⟨first, rest, descendants, recorded, winner, joined, foldCaller, foldQueries,
      folded, foldOuter, partitioned, processed, foldedCall, foldEndpoint, incomingCall,
      recordedSame, joinedValues, hole, rawTargets⟩ :=
    terminal_singleton_raw_target_incidence checkEmpty r n p h k bucket incoming caller
      before queries terminal fragment afterCaller savedQueries read after moved afterCache roots paths actual
  have foldForest := shared_fold_singleton_forest checkEmpty n p h recorded caller joined
    winner queries folded foldCaller foldQueries foldOuter foldedCall
  obtain ⟨writtenForest, compressedAliases⟩ := shared_incoming_singleton_aliases
    checkEmpty r n p h foldCaller folded winner incoming descendants foldQueries
      after afterCaller savedQueries read incomingCall
  refine ⟨first, rest, descendants, recorded, winner, joined, foldCaller, foldQueries,
    folded, foldOuter, partitioned, processed, foldedCall, foldEndpoint, incomingCall,
    recordedSame, joinedValues, hole, foldForest, writtenForest, ?_⟩
  intro sc present atRoot
  have atJoined := rawTargets sc present atRoot
  have atFolded : UnionFind.SameClass folded.representatives winner sc.var := by
    rw [foldForest]
    exact atJoined
  have atRead := compressedAliases winner sc.var atFolded
  have atReturned : UnionFind.SameClass after.representatives winner sc.var := by
    rw [writtenForest]
    exact atRead
  exact ⟨atJoined, atFolded, atRead, atReturned⟩

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
