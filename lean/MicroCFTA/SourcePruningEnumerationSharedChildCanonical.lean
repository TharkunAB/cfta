import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets
import MicroCFTA.SourcePruningEnumerationSharedDispatchShape
import MicroCFTA.SourcePruningEnumerationAssimilationCanonical
import MicroCFTA.SourcePruningEnumerationChildCanonical
import MicroCFTA.SourcePruningEnumerationPrefixCanonical
import MicroCFTA.SourcePruningEnumerationIncomingCanonical

namespace MicroCFTA.SourcePruningEnumerationSharedChildCanonical
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationIncomingNode (finish)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Canonicality through the literal shared child]
The shared dispatcher has the checked pending-assimilation shape.
The actual fold composes those successful writes in source order.
The incoming read retains values and concatenates valid stored buckets.
The successful raw terminal receipt fixes that same fold and incoming call.
The shallow route uses its checked canonical prepared action.
This proof reuses local proof text from IncomingCanonical,
TerminalCanonical, SharedChildRawAliasGrowth and ChildCanonical.
It does not identify shared native controls with the legacy dispatcher.
No resource, Total, safety or future canonicality premise is used.
-/

private theorem dispatch_canonical
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (caller : Caller width) (before : Core) (source target : Nat) (queries : Queries)
    (action : EnumerateM Symbol Constraint Unit) (reached : Caller width) (saved : Queries)
    (after : Core) (canonical : Canonical before)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      caller before source target queries = (.ok (some action), reached, saved))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) : Canonical after := by
  rcases SourcePruningEnumerationSharedDispatchShape.singleton checkEmpty nativeFuel p h
    caller before source target queries action reached saved after selected completed with
    rfl | ⟨_different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact canonical
  · exact SourcePruningEnumerationAssimilation.assimilated_canonical before source target
      sourceNode targetNode merged sourceScs targetScs canonical sourceStored targetStored

private theorem shared_fold_singleton_canonical
    (checkEmpty : Bool) (n p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Core) (target : Nat) (queries : Queries)
    (returned : Core) (afterCaller : Caller width) (savedQueries : Queries) (outer : Core)
    (canonical : Canonical before)
    (observed : SourcePruningEnumerationSharedCachedTerminal.rawFold
      checkEmpty n p h sources caller before target queries =
        (.ok (some [.ok ((), returned)]), afterCaller, savedQueries, outer)) :
    Canonical returned := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, Prod.mk.injEq,
        Except.ok.injEq, Option.some.injEq, List.cons.injEq, and_true, true_and] at observed
      rcases observed with ⟨rfl, _callerSame, _queriesSame, rfl⟩
      exact canonical
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
                          have middleCanonical := dispatch_canonical
                            checkEmpty n p h caller before source target queries action
                            reachedCaller saved middle canonical dispatchObserved rawObserved
                          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold,
                            dispatchObserved, rawObserved] at observed
                          exact ih reachedCaller middle saved middleCanonical observed

attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem finish_singleton_canonical
    {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (valid : Canonical before) (inputs : ValidSuspended incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) : Canonical returned := by
  let written : Core :=
    {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}
  have rawRun : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
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
  have oldValid : ValidSuspended oldScs :=
    valid (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)
  apply set_canonical target (.unenumerated (some handle) (incomingScs ++ oldScs)) before valid
  intro sc member
  rcases List.mem_append.mp member with incoming | old
  · exact inputs sc incoming
  · exact oldValid sc old

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem finish_reply_canonical
    {Fault : Type _} {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (valid : Canonical before) (inputs : ValidSuspended incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) : Canonical returned :=
  finish_singleton_canonical valid inputs stored (Option.some.inj (Except.ok.inj observed))

private theorem shared_incoming_run_canonical
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (valid : Canonical before) (inputs : ValidSuspended incomingScs) :
    Canonical (SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2 ∧
      ∀ returned, (SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) → Canonical returned := by
  generalize observedEq : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold SourcePruningEnumerationSharedIncomingNode.run at observedEq
  split at observedEq
  next =>
    simp only [Prod.mk.injEq] at observedEq
    rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨valid, ?_⟩
    intro returned singleton
    simp at singleton
  next =>
    repeat' first
      | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
         have resultSame := congrArg Prod.fst observedEq
         dsimp only at readSame resultSame
         constructor
         · rw [← readSame]
           change Canonical before
           exact valid
         · intro returned singleton
           rw [← resultSame] at singleton
           solve
           | simp at singleton
           | apply finish_reply_canonical (observed := singleton)
             · change Canonical before
               exact valid
             · exact inputs
             · assumption)
      | split at observedEq
      | (dsimp only at observedEq; split at observedEq)

attribute [local instance] SourcePruningEnumerationSharedCachedTerminal.sharedTerminalMonadList

private theorem raw_terminal_successful_canonical
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (outer after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (canonical : Canonical before) (inputs : ValidSuspended incomingScs)
    (observed : SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty r n p h first rest waiting caller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, outer, moved)) : Canonical after := by
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
      have joinedCanonical := SourcePruningEnumerationTerminalPrefix.run_canonical r first rest waiting
        before joined recorded winner transfer canonical prefixSuccess
      rcases foldObserved : SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty n p h recorded caller joined winner queries with
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
            have foldedCanonical := shared_fold_singleton_canonical checkEmpty n p h recorded
              caller joined winner queries folded foldCaller foldQueries foldOuter joinedCanonical foldObserved
            have incomingCanonical := shared_incoming_run_canonical checkEmpty r n p h
              foldCaller folded winner incoming incomingScs foldQueries foldedCanonical inputs
            rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                foldCaller folded winner incoming incomingScs foldQueries with
              ⟨incomingResult, reached, saved, read⟩
            rw [incomingObserved] at observed incomingCanonical
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
                exact incomingCanonical.2 after (by rw [single])
          next other => cases observed
    next other => cases observed

theorem successful_canonical
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragment : Fragment) (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (canonical : Canonical before.core) (inputs : ValidSuspended scs)
    (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after)) :
    Canonical after.core
 := by
  have coreSame := ChildDispatch.singleton_core checkEmpty r n p h k scs incoming caller reached before after
    queries saved fragment returned read waiting actual
  rw [coreSame]
  have original := (ChildDispatch.erase checkEmpty r n p h k scs incoming caller before queries).symm.trans
    (congrArg Prod.fst actual)
  by_cases empty : incoming = .empty
  · simp only [ChildDispatch.observe, empty, ↓reduceIte] at original
    cases original
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        simp only [ChildDispatch.observe, empty, ↓reduceIte, partitioned] at original
        cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
        | none => simp only [prepared] at original; cases original
        | some action =>
          rw [prepared] at original
          have rawSame := congrArg Prod.fst original
          dsimp only at rawSame
          have success : Success action before.core fragment returned := by
            rw [Success, Option.some.inj (Except.ok.inj rawSame)]
            exact List.mem_singleton_self _
          exact SourcePruningEnumerationShallowChild.prepared_canonical scs incoming before.core returned
            action fragment canonical inputs prepared success
      | cons first rest =>
        have validParts := (SourcePruningEnumerationOrdinarySemanticGates.partition_descendants scs
          (first :: rest) descendants partitioned).2 inputs
        apply raw_terminal_successful_canonical checkEmpty r n p h first rest before.waiting
          caller before.core incoming descendants queries fragment reached saved read returned
          waiting canonical validParts.2
        simpa only [ChildDispatch.observe, empty, ↓reduceIte, partitioned] using original


end MicroCFTA.SourcePruningEnumerationSharedChildCanonical
