import MicroCFTA.SourcePruningEnumerationSharedChildClassProtection
import MicroCFTA.SourcePruningEnumerationIncomingCacheProtection

/-!
# Protection at every retained shared child cache

The observation retains its original result, native caller and query endpoints.
Every retained cache protects the complete excluded class.
The proof includes fold rejection and the incoming empty sentinel write.
The source returns no cache for terminal faults or stopped raw rows.
No resource, future state or semantic assignment is a premise.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedChildIsolation
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDischargeHistory EnumerationCompressionFrame EnumerationReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

set_option autoImplicit false
variable {bits width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem actual_incoming_read_frame
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × Core)))))
    (reached : Caller width) (saved : Queries) (read : Core)
    (total : UnionFind.Total before.representatives)
    (actual : SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty r n p h caller before target incoming incomingScs queries =
        (result, reached, saved, read)) : Frame before read := by
  unfold SourcePruningEnumerationSharedIncomingNode.run at actual
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
    simp only [lookup, Prod.mk.injEq] at actual
    rcases actual with ⟨rfl, rfl, rfl, rfl⟩
    exact Frame.refl _
  | some found =>
    simp only [lookup] at actual
    have compressed : Frame before {before with representatives := found.forest} := by
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro other root size
      exact UnionFind.findRoot_reaches_iff total lookup other root size
    repeat' split at actual
    all_goals
      have readSame := congrArg
        (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) actual
      dsimp only at readSame
      rw [← readSame]
      exact compressed

private theorem actual_fold_retained_core
    (checkEmpty : Bool) (n p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (after : Cached)
    (retained : (SourcePruningEnumerationSharedCachedTerminal.fold
      checkEmpty n p h sources caller before target queries).2 = some after) :
    after.core = (SourcePruningEnumerationSharedCachedTerminal.fold
      checkEmpty n p h sources caller before target queries).1.2.2.2 := by
  induction sources generalizing caller before queries with
  | nil =>
    simp only [SourcePruningEnumerationSharedCachedTerminal.fold, Option.some.injEq] at retained
    subst after
    rfl
  | cons source rest ih =>
    rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch
      checkEmpty n p h caller before.core source target queries with
      ⟨dispatchResult, reached, saved⟩
    cases dispatchResult with
    | error fault =>
      simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
        SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved] at retained
      cases retained
    | ok possible =>
      cases possible with
      | none =>
        simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
          SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved] at retained
        cases retained
      | some action =>
        cases rawObserved : ExceptT.run (action before.core) with
        | nil =>
          simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
            SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved,
            rawObserved, SourcePruningEnumerationCachedAdapter.adapt, Option.some.injEq] at retained
          subst after
          simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
            SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved,
            rawObserved, SourcePruningEnumerationCachedAdapter.adapt]
        | cons row tail =>
          cases row with
          | error fault =>
            simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
              SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved,
              rawObserved, SourcePruningEnumerationCachedAdapter.adapt] at retained
            cases retained
          | ok pair =>
            rcases pair with ⟨⟨⟩, core⟩
            cases tail with
            | cons next remaining =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
                SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved,
                rawObserved, SourcePruningEnumerationCachedAdapter.adapt] at retained
              cases retained
            | nil =>
              cases receipt : SourcePruningEnumerationCachedAdapter.adapt
                  reached.checked.native.machine.heap before source target [.ok ((), core)] with
              | none =>
                simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
                  SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved,
                  rawObserved, receipt] at retained
                cases retained
              | some recovered =>
                simp only [SourcePruningEnumerationSharedCachedTerminal.fold,
                  SourcePruningEnumerationSharedCachedTerminal.cachedAdapter, dispatchObserved,
                  rawObserved, receipt] at retained ⊢
                exact ih reached (EnumerationExpandableIndex.frame core recovered) saved retained

/-- Every actual shared child cache protects the same original isolated class for every result tag. -/
theorem observed_retained_protected_isolated_pending
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller (bits + 2)) (before after : Cached) (queries : Queries)
    (outcome : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation (bits + 2))
    (held heldHandle : Nat) (safe : Safe before.core)
    (isolated : IsolatedPending held heldHandle before.core)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (inputs : Avoids before.core.representatives held scs)
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs value caller before queries = (outcome, some after)) :
    EnumerationDriver.Protected held before.core after.core ∧
      IsolatedPending held heldHandle after.core := by
  have retained := congrArg Prod.snd actual
  by_cases empty : value = .empty
  · simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
      ite_eq_left empty, Option.some.injEq] at retained
    subst after
    exact ⟨EnumerationDriver.Protected.refl held before.core isolated.root, isolated⟩
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        cases cached : SourcePruningEnumerationCachedPrepare.prepareChild
            caller.checked.native.machine.heap k scs value before with
        | none =>
          simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
            ite_eq_right empty, partitioned, cached] at retained
          cases retained
        | some rows =>
          cases rows with
          | nil =>
            simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
              ite_eq_right empty, partitioned, cached, Option.some.injEq] at retained
            subst after
            exact ⟨EnumerationDriver.Protected.refl held before.core isolated.root, isolated⟩
          | cons row tail =>
            rcases row with ⟨fragment, middle⟩
            cases tail with
            | cons next remaining =>
              simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
                ite_eq_right empty, partitioned, cached] at retained
              cases retained
            | nil =>
              simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
                ite_eq_right empty, partitioned, cached, Option.some.injEq] at retained
              subst after
              have erased := SourcePruningEnumerationCachedPrepare.erase_some
                caller.checked.native.machine.heap k scs value before [(fragment, middle)] cached
              cases prepared : SourcePruningEnumerationShallowChild.prepareChild
                  (EnumGuard := Constraint) scs value with
              | none => simp only [prepared, Option.map_none, reduceCtorEq] at erased
              | some action =>
                simp only [prepared, Option.map_some, Option.some.injEq, List.map_cons, List.map_nil] at erased
                have singleton : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
                    checkEmpty r n p h k scs value caller before queries =
                    ((.ok (some [.ok (fragment, middle.core)]), caller, queries,
                      before.core, before.waiting), some middle) := by
                  simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
                    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe,
                    ite_eq_right empty, partitioned, cached, prepared, erased]
                exact observed_protected_isolated_pending checkEmpty r n p h k scs value
                  caller caller before middle queries queries fragment middle.core before.core
                  before.waiting held heldHandle safe isolated bounded inputs singleton
      | cons first rest =>
        have terminalRetained : (SourcePruningEnumerationSharedCachedTerminal.run
            checkEmpty r n p h k first rest caller before value descendants queries).2 = some after := by
          simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
            ite_eq_right empty, partitioned] using retained
        have active : Avoids before.core.representatives held (first :: rest) := by
          intro sc member
          have filtered : sc ∈ scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) := by
            simpa only [List.partition_eq_filter_filter] using
              (show sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 by
                simpa only [partitioned] using member)
          exact inputs sc (List.mem_filter.mp filtered).1
        have descendantsAvoid : Avoids before.core.representatives held descendants := by
          intro sc member
          have filtered : sc ∈ scs.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) := by
            simpa only [List.partition_eq_filter_filter, Function.comp_def] using
              (show sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 by
                simpa only [partitioned] using member)
          exact inputs sc (List.mem_filter.mp filtered).1
        cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
            r first rest before.waiting before.core) with
        | nil =>
          simp only [SourcePruningEnumerationSharedCachedTerminal.run,
            ite_eq_right empty, prefixObserved] at terminalRetained
          cases terminalRetained
        | cons prefixEntry prefixTail =>
          cases prefixEntry with
          | error fault =>
            simp only [SourcePruningEnumerationSharedCachedTerminal.run,
              ite_eq_right empty, prefixObserved] at terminalRetained
            cases terminalRetained
          | ok prefixResult =>
            rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons next remaining =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.run,
                ite_eq_right empty, prefixObserved] at terminalRetained
              cases terminalRetained
            | nil =>
              have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting)
                  before.core (recorded, winner, moved) joined := by
                rw [Success, prefixObserved]
                exact List.mem_singleton_self _
              obtain ⟨joinedTotal, joinedIsolated, recordedOther, winnerSeparate, joinedClasses⟩ :=
                SourcePruningEnumerationTerminalPrefix.run_isolated r held heldHandle first rest before.waiting
                  before.core joined recorded winner moved safe.1.total isolated active prefixSuccess
              have winnerOther : winner ≠ held := by
                intro same
                subst winner
                exact winnerSeparate ⟨held, joinedIsolated.root.choose,
                  joinedIsolated.root.choose_spec, joinedIsolated.root.choose_spec⟩
              have prefixProtection : EnumerationDriver.Protected held before.core joined :=
                ⟨joinedIsolated.stored.trans isolated.stored.symm, joinedIsolated.root, joinedClasses⟩
              rcases foldObserved : SourcePruningEnumerationSharedCachedTerminal.fold checkEmpty n p h
                  recorded caller ⟨joined, before.expandable, moved⟩ winner queries with
                ⟨⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
              have erased := SourcePruningEnumerationSharedCachedTerminal.fold_erase checkEmpty n p h
                recorded caller ⟨joined, before.expandable, moved⟩ winner queries
              rw [foldObserved] at erased
              have foldFacts := shared_fold_observed_isolated_pending checkEmpty n p h recorded
                caller joined winner queries foldOutcome foldCaller foldQueries foldOuter held heldHandle
                joinedIsolated recordedOther winnerOther erased.symm
              have foldProtection : EnumerationDriver.Protected held joined foldOuter :=
                ⟨foldFacts.1.stored.trans joinedIsolated.stored.symm, foldFacts.1.root,
                  fun other => by rw [foldFacts.2]⟩
              simp only [SourcePruningEnumerationSharedCachedTerminal.run,
                ite_eq_right empty, prefixObserved, foldObserved] at terminalRetained
              cases foldOutcome with
              | error fault => cases terminalRetained
              | ok possible =>
                cases possible with
                | none => cases terminalRetained
                | some foldRaw =>
                  cases foldRaw with
                  | nil =>
                    have candidate : (SourcePruningEnumerationSharedCachedTerminal.fold checkEmpty n p h
                        recorded caller ⟨joined, before.expandable, moved⟩ winner queries).2 = some after := by
                      rw [foldObserved]
                      exact terminalRetained
                    have afterCore := actual_fold_retained_core checkEmpty n p h recorded
                      caller ⟨joined, before.expandable, moved⟩ winner queries after candidate
                    rw [foldObserved] at afterCore
                    dsimp only at afterCore
                    rw [afterCore]
                    exact ⟨prefixProtection.trans foldProtection, foldFacts.1⟩
                  | cons foldEntry foldTail =>
                    cases foldEntry with
                    | error fault => cases terminalRetained
                    | ok foldPair =>
                      rcases foldPair with ⟨⟨⟩, folded⟩
                      cases foldTail with
                      | cons next remaining => cases terminalRetained
                      | nil =>
                        have foldedSame := SourcePruningEnumerationSharedCachedTerminal.rawFold_singleton_core
                          checkEmpty n p h recorded caller joined winner queries
                          folded foldCaller foldQueries foldOuter erased.symm
                        have foldedTotal : UnionFind.Total folded.representatives := by
                          rw [foldedSame, foldFacts.2]
                          exact joinedTotal
                        have foldedIsolated : IsolatedPending held heldHandle folded := by
                          simpa only [foldedSame] using foldFacts.1
                        have foldedProtection : EnumerationDriver.Protected held before.core folded := by
                          simpa only [foldedSame] using prefixProtection.trans foldProtection
                        have foldedInputs : Avoids folded.representatives held descendants := by
                          intro sc member related
                          exact descendantsAvoid sc member ((foldedProtection.classes sc.var).mp related)
                        cases foldCache with
                        | none =>
                          dsimp only at terminalRetained
                          rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run
                              checkEmpty r n p h foldCaller folded winner value descendants foldQueries with
                            ⟨incomingOutcome, reached, saved, read⟩
                          cases incomingOutcome with
                          | error fault => simp only [incomingObserved] at terminalRetained; cases terminalRetained
                          | ok possible =>
                            cases possible <;> simp only [incomingObserved] at terminalRetained <;> cases terminalRetained
                        | some recovered =>
                          dsimp only at terminalRetained
                          rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run
                              checkEmpty r n p h foldCaller folded winner value descendants foldQueries with
                            ⟨incomingOutcome, reached, saved, read⟩
                          cases incomingOutcome with
                          | error fault =>
                            simp only [SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter,
                              EnumerationExpandableIndex.frame, incomingObserved] at terminalRetained
                            cases terminalRetained
                          | ok possible =>
                            cases possible with
                            | none =>
                              simp only [SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter,
                                EnumerationExpandableIndex.frame, incomingObserved] at terminalRetained
                              cases terminalRetained
                            | some raw =>
                              have adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt
                                  reached.checked.native.machine.heap k winner descendants
                                  (EnumerationExpandableIndex.frame folded recovered) read raw = some after := by
                                simpa only [SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter,
                                  EnumerationExpandableIndex.frame, incomingObserved] using terminalRetained
                              rcases SourcePruningEnumerationIncomingCacheAdapter.adapt_retained_shape
                                  reached.checked.native.machine.heap k winner descendants
                                  (EnumerationExpandableIndex.frame folded recovered) after read raw adapted with
                                rejected | ⟨returned, singletonRaw, _afterCore⟩
                              · subst raw
                                have readFrame := actual_incoming_read_frame checkEmpty r n p h foldCaller
                                  folded winner value descendants foldQueries (.ok (some [])) reached saved read
                                  foldedTotal incomingObserved
                                have readIsolated := foldedIsolated.through_frame readFrame
                                have readProtection : EnumerationDriver.Protected held folded read :=
                                  ⟨congrArg (fun values => values[held]?) readFrame.values, readIsolated.root,
                                    SourcePruningEnumerationNativeLanguage.frame_sameClass folded read readFrame held⟩
                                have readInputs : Avoids read.representatives held descendants := by
                                  intro sc member related
                                  exact foldedInputs sc member ((readProtection.classes sc.var).mp related)
                                obtain ⟨writtenProtection, writtenIsolated⟩ :=
                                  SourcePruningEnumerationIncomingCacheAdapter.adapt_empty_protected_isolated
                                    reached.checked.native.machine.heap k winner descendants
                                    (EnumerationExpandableIndex.frame folded recovered) after read
                                    held heldHandle readIsolated winnerOther readInputs adapted
                                exact ⟨foldedProtection.trans (readProtection.trans writtenProtection), writtenIsolated⟩
                              · subst raw
                                have cachedIncoming : SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter
                                    checkEmpty r n p h k foldCaller
                                    (EnumerationExpandableIndex.frame folded recovered) winner value descendants foldQueries =
                                    ((.ok (some [.ok ((), returned)]), reached, saved, read), some after) := by
                                  unfold SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter
                                  dsimp only [EnumerationExpandableIndex.frame]
                                  rw [incomingObserved]
                                  exact Prod.ext rfl adapted
                                have singleton : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
                                    checkEmpty r n p h k scs value caller before queries =
                                    ((.ok (some [.ok (.hole winner, returned)]), reached, saved,
                                      read, moved), some after) := by
                                  simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
                                    SourcePruningEnumerationSharedCachedTerminal.run,
                                    ite_eq_right empty, partitioned, prefixObserved, foldObserved,
                                    cachedIncoming, List.map_cons, List.map_nil]
                                exact observed_protected_isolated_pending checkEmpty r n p h k scs value
                                  caller reached before after queries saved (.hole winner) returned read moved
                                  held heldHandle safe isolated bounded inputs singleton

local notation "Fragment" => Fragments.Fragment Symbol
local notation "Child" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)

/-- Actual stored and fresh inputs protect the same class at every retained child result. -/
theorem prepared_retained_protected_isolated_pending
    (caller : Caller (bits + 2)) (captured own after : Cached)
    (parentOwner : Nat) (parentNode : Option Nat) (parentBucket : List Suspended)
    (edge : EdgeValue Symbol Constraint) (symbol : Symbol) (staged : List Child)
    (residual : Option Constraint) (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (checkEmpty : Bool) (r n p h k : Nat) (queries : Queries)
    (outcome : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation (bits + 2))
    (held heldHandle : Nat) (safe : Safe captured.core)
    (isolated : IsolatedPending held heldHandle captured.core)
    (parentStored : captured.core.values[parentOwner]? = some (.unenumerated parentNode parentBucket))
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap
      parentBucket edge captured = some [((symbol, staged, residual), own)])
    (selected : staged[position]? = some (incoming, bucket, action))
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming caller own queries = (outcome, some after)) :
    EnumerationDriver.Protected held captured.core after.core ∧
      IsolatedPending held heldHandle after.core := by
  obtain ⟨preparedProtection, ownIsolated, bucketAvoids, ownSafe, bucketBounded⟩ :=
    SourcePruningEnumerationPreparedSharedChildIsolation.prepared_stored_child_inputs
      caller captured own parentOwner parentNode parentBucket edge symbol staged residual
      position incoming bucket action held heldHandle safe isolated parentStored prepared selected
  obtain ⟨childProtection, childIsolated⟩ := observed_retained_protected_isolated_pending
    checkEmpty r n p h k bucket incoming caller own after queries outcome held heldHandle
      ownSafe ownIsolated bucketBounded bucketAvoids actual
  exact ⟨preparedProtection.trans childProtection, childIsolated⟩

end MicroCFTA.SourcePruningEnumerationSharedChildIsolation
