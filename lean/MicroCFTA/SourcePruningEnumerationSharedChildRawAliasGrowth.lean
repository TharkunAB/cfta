import MicroCFTA.SourcePruningEnumerationRawAliasPrimitives
import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets

namespace MicroCFTA.SourcePruningEnumerationSharedChildRawAliasGrowth
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationRawAliasPrimitives
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
set_option autoImplicit false

/- Note [Successful child alias growth]
The raw child receipt retains its exact supplied fuels and endpoints.
The terminal prefix performs lookup and union only.
The forward primitive laws need no totality or allocation premise.
The shared fold and incoming write retain their actual forests.
The shallow route allocates and writes a payload without changing the forest.

The local forest and interval proofs below reuse the checked proof structure
from SourcePruningEnumerationChildCarriers,
SourcePruningEnumerationSharedChildFinalRawTargets, and
SourcePruningEnumerationSharedChildRawTargets.
They use ordinary source declarations and actual successful observations.
They do not access private declaration names or replace runtime code.
The theorem does not compose a whole eager worker or identify its causal branch.
-/

private theorem shallow_prepared_forest
    (scs : List Suspended) (value : Node)
    (before after : Core)
    (action : EnumerateM Symbol Constraint Fragment) (fragment : Fragment)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs value = some action)
    (success : Success action before fragment after) :
    after.representatives = before.representatives := by
  cases value with
  | empty =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      exact (reject_unsuccessful before after fragment success).elim
  | reference name =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, reduceCtorEq] at prepared
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have writtenSame := (EnumerationDriver.modify_success _
          (allocated (some (entry.identity + 1)) before) written).mp writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        rw [writtenSame]
        rfl
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
        rfl

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

private theorem terminal_prefix_sameClass_forward
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (before after : Core)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (actual : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      fuel first rest waiting before) = [.ok ((recorded, winner, moved), after)]) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  have successful : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after := by
    rw [Success, actual]
    exact List.mem_singleton_self _
  unfold SourcePruningEnumerationTerminalPrefix.run at successful
  obtain ⟨roots, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp successful
  obtain ⟨ignored, united, joining, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨root, resolved, resolving, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨_valueSame, afterSame⟩ := (success_pure _ _ _ _).mp final
  subst after
  let invariant := fun state : Core => ∀ left right,
    UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass state.representatives left right
  have scannedAliases : invariant scanned := by
    apply mapM_invariant (fun sc : Suspended => representative fuel sc.var)
      invariant (first :: rest) ?_ before scanned roots (fun _ _ same => same) scanning
    intro sc _member current currentRoot next previous observed
    intro left right same
    exact representative_sameClass_forward fuel sc.var currentRoot current next observed
      left right (previous left right same)
  have unitedAliases : invariant united := by
    apply forM_invariant (fun sc : Suspended => unionVariables fuel first.var sc.var)
      invariant rest ?_ scanned united scannedAliases joining
    intro sc _member current next previous observed
    intro left right same
    exact unionVariables_sameClass_forward fuel first.var sc.var current next observed
      left right (previous left right same)
  intro left right same
  exact representative_sameClass_forward fuel first.var root united resolved resolving
    left right (unitedAliases left right same)

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

/-- A literal successful shared child retains every raw entry alias at both endpoints. -/
theorem successful_sameClass_forward
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragment : Fragment) (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after)) :
    after.core = returned ∧
      ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass returned.representatives left right ∧
          UnionFind.SameClass after.core.representatives left right := by
  have coreSame := ChildDispatch.singleton_core checkEmpty r n p h k scs incoming
    caller reached before after queries saved fragment returned read waiting actual
  have original := (ChildDispatch.erase checkEmpty r n p h k scs incoming caller before queries).symm.trans
    (congrArg Prod.fst actual)
  have aliases : ∀ left right, UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass returned.representatives left right := by
    by_cases empty : incoming = .empty
    · simp only [ChildDispatch.observe, empty, ↓reduceIte] at original
      cases original
    · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
      | mk here descendants =>
          cases here with
          | nil =>
              simp only [ChildDispatch.observe, empty, ↓reduceIte, partitioned] at original
              cases prepared : SourcePruningEnumerationShallowChild.prepareChild
                  (EnumGuard := Constraint) scs incoming with
              | none =>
                  simp only [prepared] at original
                  cases original
              | some action =>
                  rw [prepared] at original
                  have rawSame := congrArg Prod.fst original
                  dsimp only at rawSame
                  have successful : Success action before.core fragment returned := by
                    rw [Success, Option.some.inj (Except.ok.inj rawSame)]
                    exact List.mem_singleton_self _
                  have forest := shallow_prepared_forest scs incoming before.core returned
                    action fragment prepared successful
                  intro left right same
                  rw [forest]
                  exact same
          | cons first rest =>
              have terminalObserved : SourcePruningEnumerationSharedCachedTerminal.raw
                  checkEmpty r n p h first rest before.waiting caller before.core incoming descendants queries =
                    (.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting) := by
                simpa only [ChildDispatch.observe, empty, ↓reduceIte, partitioned] using original
              obtain ⟨recorded, winner, joined, foldCaller, foldQueries, folded, foldOuter,
                processed, foldedCall, _foldEndpoint, incomingCall, _hole⟩ :=
                raw_terminal_singleton_interval checkEmpty r n p h first rest before.waiting caller
                  before.core incoming descendants queries fragment reached saved read returned waiting terminalObserved
              have prefixAliases := terminal_prefix_sameClass_forward r first rest before.waiting
                before.core joined recorded winner waiting processed
              have foldForest := shared_fold_singleton_forest checkEmpty n p h recorded caller joined
                winner queries folded foldCaller foldQueries foldOuter foldedCall
              obtain ⟨writtenForest, incomingAliases⟩ := shared_incoming_singleton_aliases
                checkEmpty r n p h foldCaller folded winner incoming descendants foldQueries
                  returned reached saved read incomingCall
              intro left right same
              have atFolded : UnionFind.SameClass folded.representatives left right := by
                rw [foldForest]
                exact prefixAliases left right same
              rw [writtenForest]
              exact incomingAliases left right atFolded
  refine ⟨coreSame, ?_⟩
  intro left right same
  have kept := aliases left right same
  exact ⟨kept, by rw [coreSame]; exact kept⟩

end MicroCFTA.SourcePruningEnumerationSharedChildRawAliasGrowth
