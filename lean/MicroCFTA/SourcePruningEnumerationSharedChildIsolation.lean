import MicroCFTA.SourcePruningEnumerationPreparedTerminalIsolationOperations
import MicroCFTA.SourcePruningEnumerationSharedFoldState
import MicroCFTA.SourcePruningEnumerationSharedTerminalScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations

/-!
# Isolation through actual shared child observations

A successful shared child retains an original isolated root outside its inputs.
The proof follows the actual prefix, fold and incoming write.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedChildIsolation
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}

section ActualObservedSharedChildIsolation
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open EnumerationDischargeHistory EnumerationCompressionFrame EnumerationReferences
local notation "Core" => EnumerationState.State Symbol Constraint

/-- The actual shared dispatcher retains a separate isolated root. -/
private theorem shared_dispatch_observed_isolated_pending
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (caller : Caller width) (before : Core) (source target : Nat) (queries : Queries)
    (action : EnumerateM Symbol Constraint Unit) (reached : Caller width)
    (saved : Queries) (after : Core) (held heldHandle : Nat)
    (isolated : IsolatedPending held heldHandle before)
    (sourceOther : source ≠ held) (targetOther : target ≠ held)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      caller before source target queries = (.ok (some action), reached, saved))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    IsolatedPending held heldHandle after ∧ after.representatives = before.representatives := by
  have frame := SourcePruningEnumerationSharedFoldState.dispatch_frame checkEmpty nativeFuel p h
    caller before source target queries action reached saved after selected completed
  have allowed := SourcePruningEnumerationSharedFoldState.dispatch_allowed
    (fun uv => ¬UnionFind.SameClass before.representatives held uv) checkEmpty nativeFuel p h
    caller before source target queries action reached saved after isolated.incoming selected completed
  refine ⟨⟨?_, ?_, ?_⟩, frame.representatives⟩
  · simpa only [frame.representatives] using isolated.root
  · exact (frame.off_list held
      (fun member => sourceOther (List.mem_singleton.mp member).symm) (Ne.symm targetOther)).trans isolated.stored
  · intro value member sc listed same
    exact allowed value member sc listed (by simpa only [frame.representatives] using same)

-- The fold observer follows the actual shared source sequence.
private theorem shared_fold_observed_isolated_pending
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Core)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × Core)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : Core)
    (held heldHandle : Nat) (proper : IsolatedPending held heldHandle before)
    (sourcesOther : ∀ source ∈ sources, source ≠ held) (targetOther : target ≠ held)
    (observed : SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) : IsolatedPending held heldHandle after ∧ after.representatives = before.representatives := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨proper, rfl⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨proper, rfl⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨proper, rfl⟩
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨proper, rfl⟩
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact ⟨proper, rfl⟩
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          have middleFacts := shared_dispatch_observed_isolated_pending
                            checkEmpty nativeFuel p h beforeCaller before source target queries action
                            reachedCaller saved middle held heldHandle proper
                            (sourcesOther source (by simp)) targetOther dispatchObserved rawObserved
                          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved] at observed
                          have finalFacts := ih reachedCaller middle saved middleFacts.1
                            (fun next member => sourcesOther next (List.mem_cons_of_mem source member)) observed
                          exact ⟨finalFacts.1, finalFacts.2.trans middleFacts.2⟩
                      | cons second remaining =>
                          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact ⟨proper, rfl⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- The actual incoming write retains a separate isolated root. -/
private theorem shared_incoming_finish_isolated
    {before returned : Core} {target handle held heldHandle : Nat}
    {oldNode : Option Nat} {incomingScs oldScs : List Suspended} {replacement : Node}
    (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (different : target ≠ held) (inputs : Avoids before.representatives held incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) :
    UnionFind.Total returned.representatives ∧ IsolatedPending held heldHandle returned := by
  let written : Core := {before with
    values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.expansionAncestry ++ before.recursionAncestry target).eraseDups else before.recursionAncestry other}
  have rawRun : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  have singleton := observed
  rw [rawRun] at singleton
  have same : written = returned := by
    cases replacement <;>
      solve
      | cases singleton
      | exact (Prod.mk.inj (Except.ok.inj (List.cons.inj singleton).1)).2
  rw [← same]
  refine ⟨total, ⟨isolated.root, ?_, ?_⟩⟩
  · simpa only [written, List.getElem?_set_ne different] using isolated.stored
  · exact SourcePruningEnumerationNativeReferences.incoming_written
      (fun uv => ¬UnionFind.SameClass before.representatives held uv)
      before written target handle oldNode incomingScs oldScs isolated.incoming inputs stored rfl

private theorem shared_incoming_observed_isolated_pending
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (held heldHandle : Nat) (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (separate : ¬UnionFind.SameClass before.representatives held target)
    (inputs : Avoids before.representatives held incomingScs) :
    (UnionFind.Total (SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2.representatives ∧
      IsolatedPending held heldHandle
        (SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2) ∧
      ∀ returned, (SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) →
        UnionFind.Total returned.representatives ∧ IsolatedPending held heldHandle returned := by
  generalize observedEq : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold SourcePruningEnumerationSharedIncomingNode.run at observedEq
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
      simp only [lookup, Prod.mk.injEq] at observedEq
      rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨⟨total, isolated⟩, ?_⟩
      intro returned singleton
      simp at singleton
  | some found =>
      simp only [lookup] at observedEq
      have frame : Frame before {before with representatives := found.forest} := by
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        intro other root size
        exact UnionFind.findRoot_reaches_iff total lookup other root size
      have different : found.representative ≠ held :=
        representative_away before.representatives r target held separate found lookup
      have readIsolated := isolated.through_frame frame
      have readInputs : Avoids found.forest held incomingScs := by
        intro sc member related
        exact inputs sc member ((SourcePruningEnumerationNativeLanguage.frame_sameClass
          before _ frame held sc.var).mp related)
      repeat' split at observedEq
      all_goals
        have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
        have resultSame := congrArg Prod.fst observedEq
        dsimp only at readSame resultSame
        constructor
        · rw [← readSame]
          exact ⟨frame.total total, readIsolated⟩
        · intro returned singleton
          rw [← resultSame] at singleton
          try (solve | simp at singleton)
          all_goals
            exact shared_incoming_finish_isolated
              (before := {before with representatives := found.forest})
              (target := found.representative) (held := held) (heldHandle := heldHandle)
              (frame.total total) readIsolated different readInputs (by assumption)
              (Option.some.inj (Except.ok.inj singleton))

private theorem shared_terminal_observed_isolated_pending
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (outer after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (held heldHandle : Nat) (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (active : Avoids before.representatives held (first :: rest))
    (inputs : Avoids before.representatives held incomingScs)
    (observed : SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty r n p h first rest waiting caller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, outer, moved)) : IsolatedPending held heldHandle after := by
  unfold SourcePruningEnumerationSharedCachedTerminal.raw at observed
  split at observed
  next empty => cases observed
  next nonempty =>
    split at observed
    next recorded winner transfer joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest waiting)
          before (recorded, winner, transfer) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedFacts := SourcePruningEnumerationTerminalPrefix.run_isolated r held heldHandle first rest waiting
        before joined recorded winner transfer total isolated active prefixSuccess
      rcases foldObserved : SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observed
      have winnerOther : winner ≠ held := by
        intro same
        subst winner
        exact joinedFacts.2.2.2.1 (⟨held, joinedFacts.2.1.root.choose, joinedFacts.2.1.root.choose_spec, joinedFacts.2.1.root.choose_spec⟩)
      have foldFacts := shared_fold_observed_isolated_pending checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter held heldHandle joinedFacts.2.1
        joinedFacts.2.2.1 winnerOther foldObserved
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
            have foldedSame := SourcePruningEnumerationSharedCachedTerminal.rawFold_singleton_core checkEmpty n p h recorded
              caller joined winner queries folded foldCaller foldQueries foldOuter foldObserved
            have foldedIsolated : IsolatedPending held heldHandle folded := by
              simpa only [foldedSame] using foldFacts.1
            have foldedForest : folded.representatives = joined.representatives := by
              simpa only [foldedSame] using foldFacts.2
            have foldedTotal : UnionFind.Total folded.representatives := by
              rw [foldedForest]
              exact joinedFacts.1
            have separate : ¬UnionFind.SameClass folded.representatives held winner := by
              rw [foldedForest]
              exact joinedFacts.2.2.2.1
            have incomingInputs : Avoids folded.representatives held incomingScs := by
              intro sc member related
              rw [foldedForest] at related
              exact inputs sc member ((joinedFacts.2.2.2.2 sc.var).mp related)
            have incomingFacts := shared_incoming_observed_isolated_pending checkEmpty r n p h
              foldCaller folded winner incoming incomingScs foldQueries held heldHandle foldedTotal
              foldedIsolated separate incomingInputs
            rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                foldCaller folded winner incoming incomingScs foldQueries with
              ⟨incomingResult, reached, saved, read⟩
            rw [incomingObserved] at observed incomingFacts
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
                exact (incomingFacts.2 after (by rw [single])).2
          next other => cases observed
    next other => cases observed

/-- The same successful shared child singleton retains an excluded isolated root. -/
theorem observed_isolated_pending
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller (bits + 2)) (before middle : Cached) (queries saved : Queries)
    (fragment : Fragment) (returned outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting) (held heldHandle : Nat)
    (safe : Safe before.core)
    (isolated : EnumerationDischargeHistory.IsolatedPending held heldHandle before.core)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (inputs : Avoids before.core.representatives held scs)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs value caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some middle)) :
    EnumerationDischargeHistory.IsolatedPending held heldHandle middle.core := by
  have coreSame := SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.singleton_core checkEmpty r n p h k scs value caller reached before middle
    queries saved fragment returned outer waiting observed
  rw [coreSame]
  have original := (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.erase checkEmpty r n p h k scs value caller before queries).symm.trans
    (congrArg Prod.fst observed)
  by_cases empty : value = .empty
  · simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe, empty, ↓reduceIte] at original
    cases original
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe, empty, ↓reduceIte, partitioned] at original
        cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs value with
        | none => simp only [prepared] at original; cases original
        | some action =>
          rw [prepared] at original
          have rawSame := congrArg Prod.fst original
          dsimp only at rawSame
          have success : Success action before.core fragment returned := by
            rw [Success, Option.some.inj (Except.ok.inj rawSame)]
            exact List.mem_singleton_self _
          have inside : held < before.core.counter := by
            rw [safe.1.aligned]
            exact (List.getElem?_eq_some_iff.mp isolated.stored).1
          have preserved := (SourcePruningEnumerationChildEffects.child scs value action before.core returned
            fragment safe bounded prepared success).2.2 held inside isolated.root
          exact isolated.through_protected preserved scs inputs
            (fun allowed valid allowedInputs => SourcePruningEnumerationNativeReferences.prepared_allowed
              allowed scs value action before.core returned fragment valid allowedInputs prepared success)
      | cons first rest =>
        have activeMembers : (first :: rest) ⊆ scs := by
          intro sc member
          have retained : sc ∈ scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) := by
            simpa only [List.partition_eq_filter_filter] using
              (show sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 by
                simpa only [partitioned] using member)
          exact (List.mem_filter.mp retained).1
        have descendantMembers : descendants ⊆ scs := by
          intro sc member
          have retained : sc ∈ scs.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) := by
            simpa only [List.partition_eq_filter_filter, Function.comp_def] using
              (show sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 by
                simpa only [partitioned] using member)
          exact (List.mem_filter.mp retained).1
        apply shared_terminal_observed_isolated_pending checkEmpty r n p h first rest before.waiting
          caller before.core value descendants queries fragment reached saved outer returned
          waiting held heldHandle safe.1.total isolated
          (fun sc member => inputs sc (activeMembers member))
          (fun sc member => inputs sc (descendantMembers member))
        simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe, empty, ↓reduceIte, partitioned] using original

end ActualObservedSharedChildIsolation

end MicroCFTA.SourcePruningEnumerationSharedChildIsolation
