import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationSharedDispatchShape
import MicroCFTA.SourcePruningEnumerationMixedStorageProgress
import MicroCFTA.SourcePruningEnumerationTerminalPrefixBounds

/-!
# Assigned term size at actual shared child observations

A successful child charges at most the size of its returned fragment.
The assignment is fixed throughout the observation. No model is required.
Terminal folds charge only their final target and eliminate other sources.
This bound does not assert a decrease across an entire enumeration run.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedChildPendingSize
open Language EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationStorageProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

private def targetCost (state : Core) (assignment : Nat → Term Symbol) (target : Nat) : Nat :=
  match state.values[target]? with
  | some (.unenumerated (some _) _) => NumberedTerms.size (assignment target)
  | _ => 0

private theorem prefix_root
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (before after : Core)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (observed : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      fuel first rest waiting before) = [.ok ((recorded, winner, moved), after)]) :
    IsRoot after.representatives winner := by
  have success : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after := by
    simp only [Success, observed, List.mem_singleton]
  unfold SourcePruningEnumerationTerminalPrefix.run at success
  obtain ⟨actualRecorded, scanned, _scan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨ignored, united, _unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨actualWinner, resolved, resolution, finished⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resultSame, afterSame⟩ := (success_pure _ (recorded, winner, moved) resolved after).mp finished
  have winnerSame : winner = actualWinner := congrArg
    (fun result : List Nat × Nat × EnumerationWaitingIndex.Waiting => result.2.1) resultSame
  obtain ⟨found, lookup, rootSame, resolvedSame⟩ :=
    (representative_success fuel first.var united resolved actualWinner).mp resolution
  obtain ⟨path, preserved⟩ := UnionFind.findRoot_correct fuel united.representatives first.var found lookup
  rw [afterSame, resolvedSame, winnerSame, rootSame]
  exact ⟨found.size, .root (UnionFind.reaches_terminal (preserved path))⟩

private theorem finish_balance
    {before after : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (assignment : Nat → Term Symbol)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before) = [.ok ((), after)]) :
    pendingSize after assignment + targetCost before assignment target =
      pendingSize before assignment + NumberedTerms.size (assignment target) ∧
      after.counter = before.counter ∧ after.values.length = before.values.length := by
  let written : Core := {before with
    values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
      else before.recursionAncestry other}
  have actual : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by cases replacement <;> rfl
  rw [actual] at observed
  have same : written = after := by
    split at observed
    · cases observed
    · exact (Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)).2
  rw [← same]
  refine ⟨?_, rfl, by simp only [written, List.length_set]⟩
  have balance := values_set_pendingSize before target (.unenumerated oldNode oldScs)
    (.unenumerated (some handle) (incomingScs ++ oldScs)) assignment stored
  cases oldNode <;> simpa only [written, targetCost, stored, pendingSize] using balance

private theorem finish_reply_balance
    {Fault : Type _} {before after : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (assignment : Nat → Term Symbol)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : (Except.ok (some (ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before))) :
      Except Fault (Option (List (Except Error (Unit × Core))))) =
      .ok (some [.ok ((), after)])) :
    pendingSize after assignment + targetCost before assignment target =
      pendingSize before assignment + NumberedTerms.size (assignment target) ∧
      after.counter = before.counter ∧ after.values.length = before.values.length :=
  finish_balance assignment stored (Option.some.inj (Except.ok.inj observed))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem dispatch_balance
    (checkEmpty : Bool) (n p h : Nat) (beforeCaller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol Constraint Unit)
    (afterCaller : Caller width) (saved : Queries) (after : Core)
    (assignment : Nat → Term Symbol)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, saved))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    after.representatives = before.representatives ∧
      pendingSize after assignment + targetCost before assignment target ≤
        pendingSize before assignment + targetCost after assignment target ∧
      after.counter = before.counter ∧ after.values.length = before.values.length := by
  rcases SourcePruningEnumerationSharedDispatchShape.singleton checkEmpty n p h
    beforeCaller before source target queries action afterCaller saved after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs,
      sourceStored, targetStored, rfl⟩
  · exact ⟨rfl, Nat.le_refl _, rfl, rfl⟩
  · refine ⟨rfl, ?_, rfl, by simp only [assimilated, List.length_set]⟩
    have targetInside := (List.getElem?_eq_some_iff.mp targetStored).1
    have targetAfter : (assimilated before target source
        (.unenumerated merged (sourceScs ++ targetScs))).values[target]? =
        some (.unenumerated merged (sourceScs ++ targetScs)) := by
      simp [assimilated, targetInside, different]
    have balance := assimilated_pendingSize_balance before source target sourceNode targetNode merged
      sourceScs targetScs assignment (Ne.symm different) sourceStored targetStored
    cases sourceNode <;> cases targetNode <;> cases merged <;>
      simp only [targetCost, targetStored, targetAfter, Option.isSome_none, Option.isSome_some,
        Bool.false_eq_true, ↓reduceIte] at balance ⊢ <;> omega

private theorem fold_balance
    (checkEmpty : Bool) (n p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Core) (target : Nat) (queries : Queries)
    (afterCaller : Caller width) (saved : Queries) (after outer : Core)
    (assignment : Nat → Term Symbol)
    (observed : SourcePruningEnumerationSharedCachedTerminal.rawFold
      checkEmpty n p h sources beforeCaller before target queries =
      (.ok (some [.ok ((), after)]), afterCaller, saved, outer)) :
    after.representatives = before.representatives ∧
      pendingSize after assignment + targetCost before assignment target ≤
        pendingSize before assignment + targetCost after assignment target ∧
      after.counter = before.counter ∧ after.values.length = before.values.length := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
    simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, Prod.mk.injEq,
      Except.ok.injEq, Option.some.injEq, List.cons.injEq, and_true, true_and] at observed
    rcases observed with ⟨rfl, _caller, _queries, rfl⟩
    exact ⟨rfl, Nat.le_refl _, rfl, rfl⟩
  | cons source rest ih =>
    rcases selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
        beforeCaller before source target queries with ⟨result, reachedCaller, savedQueries⟩
    cases result with
    | error fault =>
      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, selected] at observed
      cases observed
    | ok possible =>
      cases possible with
      | none =>
        simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, selected] at observed
        cases observed
      | some action =>
        cases raw : ExceptT.run (action before) with
        | nil =>
          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, selected, raw] at observed
          cases observed
        | cons first tail =>
          cases first with
          | error fault =>
            simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, selected, raw] at observed
            cases observed
          | ok pair =>
            rcases pair with ⟨ignored, middle⟩
            cases ignored
            cases tail with
            | cons second remaining =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, selected, raw] at observed
              cases observed
            | nil =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, selected, raw] at observed
              have head := dispatch_balance checkEmpty n p h beforeCaller before source target queries
                action reachedCaller savedQueries middle assignment selected raw
              have tail := ih reachedCaller middle savedQueries observed
              have headCost := head.2.1
              have tailCost := tail.2.1
              exact ⟨tail.1.trans head.1, by omega,
                tail.2.2.1.trans head.2.2.1, tail.2.2.2.trans head.2.2.2⟩

private theorem incoming_balance
    (checkEmpty : Bool) (r n p h : Nat) (beforeCaller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (afterCaller : Caller width) (saved : Queries) (after read : Core)
    (assignment : Nat → Term Symbol) (root : IsRoot before.representatives target)
    (observed : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
      beforeCaller before target incoming incomingScs queries =
      (.ok (some [.ok ((), after)]), afterCaller, saved, read)) :
    pendingSize after assignment + targetCost before assignment target =
      pendingSize before assignment + NumberedTerms.size (assignment target) ∧
      after.counter = before.counter ∧ after.values.length = before.values.length := by
  unfold SourcePruningEnumerationSharedIncomingNode.run at observed
  split at observed
  next => simp at observed
  next found foundRun =>
    obtain ⟨path, _preserved⟩ := UnionFind.findRoot_correct r before.representatives target found foundRun
    obtain ⟨_size, rootPath⟩ := root
    have same : found.representative = target := (UnionFind.reaches_unique path rootPath).1
    simp only [same] at observed
    repeat' first
      | solve
        | simp at observed
        | have balance := finish_reply_balance assignment (by assumption) (congrArg Prod.fst observed)
          simpa only [pendingSize, targetCost] using balance
      | split at observed
      | (dsimp only at observed; split at observed)

private theorem terminal_pendingSize_le
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (beforeCaller : Caller width) (before : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (afterCaller : Caller width) (saved : Queries) (fragment : Fragment)
    (after outer : Core) (moved : EnumerationWaitingIndex.Waiting)
    (assignment : Nat → Term Symbol)
    (observed : SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty r n p h
      first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, saved, outer, moved)) :
    pendingSize after assignment ≤ pendingSize before assignment +
      NumberedTerms.size (Fragments.fill assignment fragment) ∧
      after.counter = before.counter ∧ after.values.length = before.values.length := by
  by_cases empty : incoming = .empty
  · simp [SourcePruningEnumerationSharedCachedTerminal.raw, empty] at observed
  · cases prefixRun : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        r first rest waiting before) with
    | nil => simp [SourcePruningEnumerationSharedCachedTerminal.raw, empty, prefixRun] at observed
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error fault => simp [SourcePruningEnumerationSharedCachedTerminal.raw, empty, prefixRun] at observed
      | ok prefixValue =>
        rcases prefixValue with ⟨⟨recorded, winner, shifted⟩, joined⟩
        cases prefixTail with
        | cons second remaining =>
          simp [SourcePruningEnumerationSharedCachedTerminal.raw, empty, prefixRun] at observed
        | nil =>
          rcases foldedRun : SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty n p h
              recorded beforeCaller joined winner queries with ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
          simp only [SourcePruningEnumerationSharedCachedTerminal.raw, ite_eq_right empty,
            prefixRun, foldedRun] at observed
          cases foldResult with
          | error fault => cases observed
          | ok possible =>
            cases possible with
            | none => cases observed
            | some rows =>
              cases rows with
              | nil => cases observed
              | cons firstRow restRows =>
                cases firstRow with
                | error fault => cases observed
                | ok foldPair =>
                  rcases foldPair with ⟨ignored, folded⟩
                  cases ignored
                  cases restRows with
                  | cons second remaining => cases observed
                  | nil =>
                    rcases incomingRun : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                        foldCaller folded winner incoming incomingScs foldQueries with
                        ⟨incomingResult, reachedCaller, reachedQueries, reachedRead⟩
                    simp only [incomingRun] at observed
                    cases incomingResult with
                    | error fault => cases observed
                    | ok possible =>
                      cases possible with
                      | none => cases observed
                      | some incomingRows =>
                        have mapped := Option.some.inj (Except.ok.inj (congrArg Prod.fst observed))
                        obtain ⟨row, rowsSame, rowSame⟩ := List.map_eq_singleton_iff.mp mapped
                        cases row with
                        | error fault => cases rowSame
                        | ok pair =>
                          rcases pair with ⟨ignored, returned⟩
                          cases ignored
                          obtain ⟨fragmentSame, afterSame⟩ := Prod.mk.inj (Except.ok.inj rowSame)
                          subst fragment
                          change returned = after at afterSame
                          subst returned
                          have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run
                              r first rest waiting) before (recorded, winner, shifted) joined := by
                            simp only [Success, prefixRun, List.mem_singleton]
                          have frame := SourcePruningEnumerationTerminalPrefix.success_frame
                            r first rest waiting before joined (recorded, winner, shifted) prefixSuccess
                          have prefixCost : pendingSize joined assignment = pendingSize before assignment := by
                            rw [frame]
                            rfl
                          have foldCost := fold_balance checkEmpty n p h recorded beforeCaller joined winner
                            queries foldCaller foldQueries folded foldOuter assignment foldedRun
                          have rooted : IsRoot folded.representatives winner := by
                            rw [foldCost.1]
                            exact prefix_root r first rest waiting before joined recorded winner shifted prefixRun
                          have incomingActual : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                              foldCaller folded winner incoming incomingScs foldQueries =
                              (.ok (some [.ok ((), after)]), reachedCaller, reachedQueries, reachedRead) := by
                            simpa only [rowsSame] using incomingRun
                          have incomingCost := incoming_balance checkEmpty r n p h foldCaller folded winner
                            incoming incomingScs foldQueries reachedCaller reachedQueries after reachedRead
                            assignment rooted incomingActual
                          have prefixCounter := congrArg (fun state : Core => state.counter) frame
                          have prefixLength := congrArg (fun state : Core => state.values.length) frame
                          change joined.counter = before.counter at prefixCounter
                          change joined.values.length = before.values.length at prefixLength
                          refine ⟨?_, incomingCost.2.1.trans
                            (foldCost.2.2.1.trans prefixCounter),
                            incomingCost.2.2.trans
                            (foldCost.2.2.2.trans prefixLength)⟩
                          have written := incomingCost.1
                          have foldedCost := foldCost.2.1
                          simp only [Fragments.fill]
                          omega

end MicroCFTA.SourcePruningEnumerationSharedChildPendingSize

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates
open EnumerationStorageProgress SourcePruningEnumerationSharedChildPendingSize
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

private theorem shallow_pendingSize_le
    (scs : List Suspended) (incoming : Node) (before after : Core)
    (action : EnumerateM Symbol Constraint Fragment) (fragment : Fragment)
    (assignment : Nat → Term Symbol) (aligned : before.counter = before.values.length)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (observed : ExceptT.run (action before) = [.ok (fragment, after)]) :
    pendingSize after assignment ≤ pendingSize before assignment +
      NumberedTerms.size (Fragments.fill assignment fragment) ∧
      after.counter = after.values.length := by
  cases incoming with
  | empty =>
    simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
    subst action
    cases observed
  | reference name => simp [SourcePruningEnumerationShallowChild.prepareChild] at prepared
  | node entry edges depth free =>
    by_cases blocked : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, blocked] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, blocked, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before) before.counter
      (allocate_exact _ _)] at observed
    change [Except.ok ((.hole before.counter : Fragment),
      {allocated (some (entry.identity + 1)) before with
        values := (allocated (some (entry.identity + 1)) before).values.set before.counter
          (.unenumerated (some (entry.identity + 1)) scs)})] = _ at observed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)
    refine ⟨?_, ?_⟩
    · have allocatedCost := allocate_pendingSize (some (entry.identity + 1)) before
        (allocated (some (entry.identity + 1)) before) before.counter assignment assignment aligned
        (fun _ _ => rfl) (by simp only [Success, allocate_exact, ExceptT.run, List.mem_singleton])
      have writtenCost := values_set_pendingSize (allocated (some (entry.identity + 1)) before)
        before.counter (.unenumerated (some (entry.identity + 1)) [])
        (.unenumerated (some (entry.identity + 1)) scs) assignment
        (allocated_slot _ _ aligned)
      change pendingSize _ assignment + NumberedTerms.size (assignment before.counter) =
        pendingSize (allocated (some (entry.identity + 1)) before) assignment +
          NumberedTerms.size (assignment before.counter) at writtenCost
      simp only [Fragments.fill] at ⊢
      simp only at allocatedCost
      omega
    · simpa only [List.length_set] using allocated_supply (some (entry.identity + 1)) before aligned
  | union entry members depth free | mu entry body depth free =>
    by_cases blocked : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, blocked] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, blocked, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before) before.counter
      (allocate_exact _ _)] at observed
    change [Except.ok ((.hole before.counter : Fragment),
      allocated (some (entry.identity + 1)) before)] = _ at observed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)
    have cost := allocate_pendingSize (some (entry.identity + 1)) before
      (allocated (some (entry.identity + 1)) before) before.counter assignment assignment aligned
      (fun _ _ => rfl) (by simp only [Success, allocate_exact, ExceptT.run, List.mem_singleton])
    exact ⟨by simpa only [Fragments.fill] using Nat.le_of_eq cost,
      allocated_supply (some (entry.identity + 1)) before aligned⟩

private theorem singleton_bounds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : Cached) (queries : Queries)
    (reachedCaller : Caller width) (after : Cached) (savedQueries : Queries)
    (fragment : Fragment) (returned outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (assignment : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (observed : run checkEmpty r n p h k scs incoming beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    pendingSize after.core assignment ≤ pendingSize before.core assignment +
      NumberedTerms.size (Fragments.fill assignment fragment) ∧
      after.core.counter = after.core.values.length := by
  have same := singleton_core checkEmpty r n p h k scs incoming beforeCaller reachedCaller
    before after queries savedQueries fragment returned outer waiting observed
  rw [same]
  have raw := congrArg Prod.fst observed
  rw [erase] at raw
  by_cases empty : incoming = .empty
  · simp [observe, empty] at raw
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        cases prepared : SourcePruningEnumerationShallowChild.prepareChild
            (EnumGuard := Constraint) scs incoming with
        | none =>
          simp only [observe, ite_eq_right empty, partitioned, prepared] at raw
          cases raw
        | some action =>
          simp only [observe, ite_eq_right empty, partitioned, prepared] at raw
          exact shallow_pendingSize_le scs incoming before.core returned action fragment assignment aligned
            prepared (Option.some.inj (Except.ok.inj (congrArg Prod.fst raw)))
      | cons first rest =>
        simp only [observe, ite_eq_right empty, partitioned] at raw
        have bounds := terminal_pendingSize_le checkEmpty r n p h first rest beforeCaller before.core before.waiting
          incoming descendants queries reachedCaller savedQueries fragment returned outer waiting assignment raw
        exact ⟨bounds.1, by rw [bounds.2.1, bounds.2.2]; exact aligned⟩

/-- Every actual successful child charges at most its filled fragment's size. -/
theorem singleton_pendingSize_le
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : Cached) (queries : Queries)
    (reachedCaller : Caller width) (after : Cached) (savedQueries : Queries)
    (fragment : Fragment) (returned outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (assignment : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (observed : run checkEmpty r n p h k scs incoming beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    pendingSize after.core assignment ≤ pendingSize before.core assignment +
      NumberedTerms.size (Fragments.fill assignment fragment) :=
  (singleton_bounds checkEmpty r n p h k scs incoming beforeCaller before queries reachedCaller after
    savedQueries fragment returned outer waiting assignment aligned observed).1

/-- A successful child retains allocation alignment at its literal returned cache. -/
theorem singleton_aligned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {beforeCaller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (aligned : before.core.counter = before.core.values.length)
    (observed : run checkEmpty r n p h k scs incoming beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    after.core.counter = after.core.values.length :=
  (singleton_bounds checkEmpty r n p h k scs incoming beforeCaller before queries reachedCaller after
    savedQueries fragment returned outer waiting (fun _ => .node ("", FullSyntax.Formula.top) []) aligned observed).2

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
